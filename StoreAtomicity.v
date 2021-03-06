(* Copyright (c) 2015 Muralidaran Vijayaraghavan vmurali@csail.mit.edu *)


(* Permission is hereby granted, free of charge, to any person obtaining *)
(* a copy of this software and associated documentation files (the *)
(* "Software"), to deal in the Software without restriction, including *)
(* without limitation the rights to use, copy, modify, merge, publish, *)
(* distribute, sublicense, and/or sell copies of the Software, and to *)
(* permit persons to whom the Software is furnished to do so, subject to *)
(* the following conditions: *)

(* The above copyright notice and this permission notice shall be *)
(* included in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE *)
(* LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION *)
(* OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION *)
(* WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. *)


Require Import SeqConsistency.TransitionsNew SeqConsistency.DataTypes SeqConsistency.Useful.

Set Implicit Arguments.

Section AddrDataProc.
  Variable Addr Data Proc: Set.
  Variable zero: Addr.
  Variable decAddr: forall a1 a2: Addr, {a1=a2}+{a1<>a2}.
  Variable initData: Addr -> Data.
  Inductive InstantMemory m : (Addr -> Data) -> Set :=
  | IReq a (p: Proc) d (w: Desc):
      InstantMemory m (if w
                       then m
                       else 
                         fun a' => 
                           if decAddr a a'
                           then d
                           else m a')
  | IIdle: InstantMemory m m.

  Definition getImIo s s' (t: InstantMemory s s') :=
    match t with
      | IReq a p d w => Some (a, p, d, w, if w
                                          then s a
                                          else initData zero)
      | IIdle => None
    end.

  Section CreateInstantMemory.
    Variable State: Set.
    Variable Trans: AllTransitions State.
    Variable initState: State.
    Variable stm: Stream Trans initState.
    Variable getTransIo: forall s s',
                           Trans s s' -> option (Addr * Proc * Data * Desc * Data). 
    Record StoreAtomicity := {
                              storeAtomicityLd:
                                forall t a c d ld,
                                  getStreamIo getTransIo t stm = Some (a, c, d, Ld, ld) ->
                                  (ld = initData a /\
                                   forall {ti}, 0 <= ti < t ->
                                                forall ci di ldi,
                                                  ~ getStreamIo getTransIo ti stm = Some (a, ci, di, St, ldi)) \/
                                  (exists cb tb ldb,
                                     tb < t /\
                                     getStreamIo getTransIo tb stm = Some (a, cb, ld, St, ldb) /\
                                     forall ti, tb < ti < t ->
                                                forall ci di ldi,
                                                  ~ getStreamIo getTransIo ti stm = Some (a, ci, di, St, ldi));

                              storeAtomicitySt:
                                forall t a c d ld,
                                  getStreamIo getTransIo t stm = Some (a, c, d, St, ld) ->
                                  ld = initData zero }.

    Fixpoint getNStateForStm x :=
      match x with
        | 0 => initData
        | S m => match getStreamIo getTransIo m stm with
                   | Some (a, c, d, w, ld) => if w
                                              then getNStateForStm m
                                              else fun a' =>
                                                     if decAddr a a'
                                                     then d
                                                     else (getNStateForStm m) a'
                   | None => getNStateForStm m
                 end
      end.

    CoFixpoint buildIm n: Stream InstantMemory (getNStateForStm n) :=
      TCons _
            (match getStreamIo getTransIo n stm as io return InstantMemory (getNStateForStm n)
                                                                           match io with
                                                                             | Some (a, c, d, w, ld) => if w
                                                                                                        then getNStateForStm n
                                                                                                        else fun a' => if decAddr a a'
                                                                                                                       then d
                                                                                                                       else (getNStateForStm n) a'
                                                                             | None => getNStateForStm n
                                                                           end
             with
               | Some (a, c, d, w, ld) => IReq (getNStateForStm n) a c d w
               | None => IIdle (getNStateForStm n)
             end) (eq_rect_r _ (buildIm (S n)) eq_refl).


    Theorem buildImSth n:
      forall m,
        match getStreamIo getTransIo (n+m) stm, getStreamIo getImIo n (buildIm m) with
          | Some (a, c, d, w, ld), Some (a', c', d', w', ld') =>
            a = a' /\ c = c' /\ d = d' /\ w = w' /\
            ld' = if w then getNStateForStm (n+m) a else initData zero
          | None, None => True
          | _, _ => False
        end.
    Proof.
      unfold getStreamIo, getImIo.
      induction n.
      intros.
      simpl in *.
      unfold getStreamIo.
      destruct (getTransIo (getStreamTransition stm m)).
      destruct p,p,p,p; intuition.
      intuition.
      intros.
      specialize (IHn (S m)).
      assert (n + S m = S n + m) by omega.
      rewrite H in *.
      assumption.
    Qed.
  End CreateInstantMemory.

  Section AllSa.
    Theorem memGood' t:
      forall s (stm: Stream InstantMemory s) a,
        (fst (getStreamState t stm) a = s a /\
         forall ti,
           0 <= ti < t ->
           forall ci di ldi,
             ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)) \/
        (exists cb tb ldb,
           tb < t /\
           getStreamIo getImIo tb stm =
           Some (a, cb, fst (getStreamState t stm) a, St, ldb) /\
           forall ti, tb < ti < t ->
                      forall ci di ldi,
                        ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)).
    Proof.
      unfold getStreamIo in *.
      induction t.
      intros.
      simpl in *.
      destruct stm; simpl.
      left; (reflexivity || intuition; assert False by omega; intuition).

      intros.

      simpl in *.
      destruct stm; simpl.

      destruct i; intros; simpl in *.
      destruct w.

      destruct (IHt _ stm a) as [[cond nopast]|past].

      left; intros.
      constructor.
      assumption.
      intros;
        destruct ti; simpl in *.
      discriminate.
      assert (0 <= ti < t) by omega;
        apply (nopast); intuition.

      right; intros.
      match goal with
        | H: exists cb tb ld, _ |- _ =>
          destruct H as [cb [tb [ldb [eq1 [eq2 rest]]]]];
            exists cb, (S tb), ld
      end.
      constructor; (omega || intuition).

      destruct ti.
      omega.
      simpl in H.
      assert (tb < ti < t) by omega.
      apply (rest (ti) H2 ci di ldi H).


      destruct (decAddr a0 a); intros.
      rewrite <- e in *.

      right.
      destruct (IHt _ stm a) as [[cond nopast]|past]; clear IHt.

      exists p, 0, (initData zero).

      constructor.
      omega.
      simpl.
      constructor.
      destruct (decAddr a0 a).
      destruct (decAddr a0 a0); intuition.

      rewrite <- e in *.
      rewrite cond in *.
      intuition.
      intuition.
      intros.

      destruct ti.
      omega.
      simpl in *.
      rewrite <- e in *.
      assert (H2: 0 <= ti < t) by omega.
      apply (nopast _ H2 ci di ldi).

      match goal with
        | H: exists cb tb ld, _ |- _ =>
          destruct H as [cb [tb [ldb [eq1 [eq2 rest]]]]];
            exists cb, (S tb), ld
      end.
      constructor; (omega || intuition).

      rewrite <- e in *.
      intuition.

      destruct ti.
      omega.
      simpl in *.
      assert (tb < ti < t) by omega.
      rewrite <- e in *.
      apply (rest (ti) H2 ci di ldi H).

      destruct (decAddr a0 a).
      intuition.

      destruct (IHt _ stm a) as [[cond nopast] | past]; clear IHt.
      
      destruct (decAddr a0 a).
      intuition.

      left; intros.
      constructor.
      assumption.
      intros;
        destruct ti; simpl in *.
      unfold not; intros. injection H0; intros.
      intuition.
      assert (0 <= ti < t) by omega;
        apply (nopast); intuition.

      right; intros.
      match goal with
        | H: exists cb tb ld, _ |- _ =>
          destruct H as [cb [tb [ldb [eq1 [eq2 rest]]]]];
            exists cb, (S tb), ld
      end.
      constructor; (omega || intuition).

      destruct ti.
      omega.
      simpl in H.
      assert (tb < ti < t) by omega.
      apply (rest (ti) H2 ci di ldi H).

      specialize (IHt _ stm a).
      destruct IHt as [[cond nopast] | past].

      left; intros.
      constructor.
      assumption.
      intros; destruct ti; simpl in *.
      discriminate.

      assert (0 <= ti < t) by omega;
        apply nopast; intuition.

      right; intros.

      match goal with
        | H: exists cb tb ld, _ |- _ =>
          destruct H as [cb [tb [ldb [eq1 [eq2 rest]]]]];
            exists cb, (S tb), ld
      end.
      constructor; (omega || intuition).

      destruct ti.
      omega.

      simpl in H.
      assert (tb < ti < t) by omega.
      apply (rest (ti) H2 ci di ldi H).
    Qed.

    Theorem storeAtomicityLd':
      forall mem (stm: Stream InstantMemory mem) t a c d ld,
        getStreamIo getImIo t stm = Some (a, c, d, Ld, ld) ->
        (ld = mem a /\
         forall {ti}, 0 <= ti < t -> forall ci di ldi, 
                                       ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)) \/
        (exists cb tb ldb, tb < t /\ getStreamIo getImIo tb stm = Some (a, cb, ld, St, ldb) /\
                           forall ti, tb < ti < t ->
                                      forall ci di ldi, 
                                        ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)).
    Proof.
      pose proof memGood'.
      intros.
      specialize (H t mem stm a).
      unfold getStreamIo, getImIo in *.
      destruct (getStreamTransition stm t).
      injection H0. intros.

      rewrite H2, H3, H4, H5, H1 in *.
      destruct H.
      left.
      intuition.
      right.

      destruct H as [cb [tb [ldb rest]]].
      exists cb, tb, ldb.
      intuition.
      discriminate.
    Qed.

    Theorem storeAtomicitySt':
      forall s (stm: Stream InstantMemory s) t a c d ld,
        getStreamIo getImIo t stm = Some (a, c, d, St, ld) ->
        ld = initData zero.
    Proof.
      intros.
      unfold getImIo, getStreamIo in *.
      destruct (getStreamTransition stm t).
      destruct w.
      discriminate.
      injection H; auto.
      discriminate.
    Qed.

    Definition saInstMem (stm: Stream InstantMemory initData) 
      := Build_StoreAtomicity
           stm getImIo (storeAtomicityLd' stm) (storeAtomicitySt' stm).
  End AllSa.

  Section Final.
    Variable State: Set.
    Variable Trans: AllTransitions State.
    Variable initState: State.
    Variable stm: Stream Trans initState.
    Variable (getTransIo: forall s s', Trans s s' -> option (Addr * Proc * Data * Desc * Data)).
    Variable sa: StoreAtomicity stm getTransIo.

    Theorem buildImSimulate:
      forall n,
        getStreamIo getTransIo n stm = getStreamIo getImIo n (buildIm stm getTransIo 0).
    Proof.
      apply (@strong_ind' (fun n => getStreamIo getTransIo n stm = getStreamIo getImIo n
                                                                               (buildIm stm getTransIo 0))).
      simpl in *.
      destruct sa as [sLd sSt].

      pose proof (saInstMem (buildIm stm getTransIo 0)) as [bLd bSt].
      specialize (sLd 0).
      specialize (sSt 0).
      specialize (bLd 0).
      specialize (bSt 0).

      pose proof (buildImSth stm getTransIo 0 0) as sth; assert (H:0+0 = 0) by omega;
      rewrite H in *; clear H.

      simpl in *.

      destruct (getStreamIo getTransIo 0 stm).
      destruct p, p, p, p.
      specialize (sLd a p d1 d).
      specialize (sSt a p d1 d).
      specialize (bLd a p d1 (if d0 then getNStateForStm stm getTransIo 0 a else initData zero)).
      specialize (bSt a p d1 (if d0 then getNStateForStm stm getTransIo 0 a else initData zero)).

      case_eq (getStreamIo getImIo 0 (buildIm stm getTransIo 0)); intros.
      simpl in H, sth.
      rewrite H in *; clear H.
      destruct p0, p0, p0, p0.
      destruct sth as [u1 [u2 [u3 [u4 u5]]]].
      rewrite u1, u2, u3, u4, u5 in *; clear u1 u2 u3 u4.
      repeat f_equal.

      destruct d3.

      assert (Some (a0, p0, d4, Ld, d) = Some (a0, p0, d4, Ld, d)) by reflexivity.
      specialize (sLd H); clear H.
      assert (Some (a0, p0, d4, Ld, getNStateForStm stm getTransIo 0 a0) =
              Some (a0, p0, d4, Ld, getNStateForStm stm getTransIo 0 a0)) by reflexivity.
      specialize (bLd H); clear H.

      destruct sLd, bLd.
      intuition.
      intuition.
      destruct H as [_ [tb [_ [x _]]]].
      assert False by omega; intuition.
      destruct H as [_ [tb [_ [x _]]]].
      assert False by omega; intuition.

      assert (Some (a0, p0, d4, St, d) = Some (a0, p0, d4, St,d)) by reflexivity.
      apply (sSt H).


      simpl in H, sth.
      rewrite H in *; clear H.
      intuition.

      case_eq (getStreamIo getImIo 0 (buildIm stm getTransIo 0)); intros.
      simpl in H, sth.
      rewrite H in *; clear H.
      intuition.
      auto.



      intros n IHn.




      simpl in *.
      destruct sa as [sLd sSt].

      pose proof (saInstMem (buildIm stm getTransIo 0)) as [bLd bSt].
      specialize (sLd (S n)).
      specialize (sSt (S n)).
      specialize (bLd (S n)).
      specialize (bSt (S n)).

      pose proof (buildImSth stm getTransIo (S n) 0) as sth; assert (H:S n+0 = S n) by omega;
      rewrite H in *; clear H.


      destruct (getStreamIo getTransIo (S n) stm).
      destruct p, p, p, p.
      specialize (sLd a p d1 d).
      specialize (sSt a p d1 d).
      specialize (bLd a p d1 (if d0 then getNStateForStm stm getTransIo (S n) a else initData zero)).
      specialize (bSt a p d1 (if d0 then getNStateForStm stm getTransIo (S n) a else initData zero)).

      case_eq (getStreamIo getImIo (S n) (buildIm stm getTransIo 0)); intros.
      simpl in H.
      unfold getNStateForStm at 1 in sth.
      rewrite H in *; clear H.
      destruct p0, p0, p0, p0.
      destruct sth as [u1 [u2 [u3 [u4 u5]]]].
      rewrite u1, u2, u3, u4, u5 in *.
      clear u1 u2 u3 u4.
      repeat f_equal.

      destruct d3.

      assert (Some (a0, p0, d4, Ld, d) = Some (a0, p0, d4, Ld, d)) by reflexivity.
      specialize (sLd H); clear H.
      assert (Some (a0, p0, d4, Ld, getNStateForStm stm getTransIo (S n) a0) =
              Some (a0, p0, d4, Ld, getNStateForStm stm getTransIo (S n) a0)) by reflexivity.
      specialize (bLd H); clear H.

      destruct sLd, bLd.
      destruct H as [u1 _]; destruct H0 as [u2 _].
      rewrite <- u2 in u1.
      assumption.

      destruct H as [_ u1]; destruct H0 as [cb [tb [ldb [lt [eq _]]]]].
      assert (0 <= tb < S n) by omega.
      rewrite <- u5 in eq.
      assert (H0: tb <= n) by omega.
      specialize (IHn tb H0).
      rewrite <- IHn in eq.
      specialize (u1 tb H cb d2 ldb eq); intuition.

      destruct H0 as [_ u1]; destruct H as [cb [tb [ldb [lt [eq _]]]]].
      assert (0 <= tb < S n) by omega.
      assert (H0: tb <= n) by omega.
      specialize (IHn tb H0).
      rewrite IHn in eq.
      specialize (u1 tb H cb d ldb eq); intuition.






      destruct H as [cb [tb [ldb [lt [eq rest] ]]]];
        destruct H0 as [cb' [tb' [ldb' [lt' [eq' rest']]]]].


      assert (opts:tb = tb' \/ tb < tb' \/ tb > tb') by omega.

      destruct opts as [ez | [hard1  | hard2]].

      rewrite ez in *.

      assert (H: tb' <= n) by omega.
      specialize (IHn tb' H).
      rewrite IHn in *.
      rewrite eq in eq'.
      injection eq'; intros; assumption.


      specialize (rest tb' (conj hard1 lt') cb' (getNStateForStm stm getTransIo (S n) a0) ldb').
      assert (H: tb' <= n) by omega.
      specialize (IHn tb' H).
      rewrite IHn in *.
      intuition.


      specialize (rest' tb (conj hard2 lt) cb d ldb).
      assert (H: tb <= n) by omega.
      specialize (IHn tb H).
      rewrite IHn in *.
      intuition.

      assert (Some (a0, p0, d4, St, d) = Some (a0, p0, d4, St, d)) by reflexivity.
      intuition.


      rewrite H in *.
      intuition.


      case_eq (getStreamIo getImIo (S n) (buildIm stm getTransIo 0)); intros.
      simpl in H.
      unfold getNStateForStm at 1 in sth.
      rewrite H in *; clear H.
      intuition.

      auto.
    Qed.

    Theorem actualSimThm:
      exists b1 (sb1: Stream InstantMemory b1),
        forall n,
          getStreamIo getTransIo n stm = getStreamIo getImIo n sb1.
    Proof.
      exists initData, (buildIm stm getTransIo 0).
      apply (@buildImSimulate).
    Qed.

  End Final.
End AddrDataProc.
