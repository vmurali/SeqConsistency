Require Import DataTypes Transitions Useful.

Set Implicit Arguments.

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
    forall m a c d w ld,
      getStreamIo getTransIo (m+n) stm = Some (a, c, d, w, ld) ->
      getStreamIo getImIo m (buildIm n) = Some (a, c, d, w, if w
                                                            then getNStateForStm (m+n) a
                                                            else initData zero).
  Proof.
    unfold getStreamIo, getImIo.
    induction n.
    intros.
    assert (H2: m+0 = m) by omega; rewrite H2 in *; clear H2.
    simpl in *.
    unfold getStreamIo in *.
    destruct (getStreamTransition (buildIm 0) m).
    destruct (getTransIo (getStreamTransition stm m)).
    destruct p, p, p, p.
    injection H; intros.
    repeat f_equal; subst; intuition.
    discriminate.

    intros.
    assert (H0: S m + n = m + S n) by omega.
    specialize (IHn (S m) a c d w ld).
    rewrite H0 in *.
    rewrite H in *.
    assert (K: Some (a, c,d,w,ld) = Some (a,c,d,w,ld)) by reflexivity.
    specialize (IHn K).
    simpl in *.
    simpl in *.
    rewrite H1, H4 in *.
    reflexivity.
    auto
      match getStreamIo getTransIo (m+n) stm, getStreamIo getImIo 0 (buildIm m) with
        | Some (a, c, d, w, ld), Some (a', c', d', w', ld') =>
            a = a' /\ c = c' /\ d = d' /\ w = w' /\ ld = if w'
                                                         then getNStateForStm (m+n) a
                                                         else initData zero
        | None, None => True
        | _, _ => False
      end.
  Proof.
    unfold getStreamIo, getImIo.
    induction n.
    intros m.
    assert (m+0 = m) by omega.
    rewrite H.
    simpl.
    destruct (getTran

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

  Theorem buildImSimulate n (stm: Stream Trans initState):
    forall (getTransIo: forall s s', Trans s s' -> option (Addr * Proc * Data * Desc * Data)),
      StoreAtomicity stm getTransIo ->
      getStreamIo getTransIo n stm = getStreamIo getImIo n (buildIm stm getTransIo 0).
  Proof.
    intros getTransIo [sLd sSt].
    pose proof (saInstMem (buildIm stm getTransIo 0)) as [bLd bSt].
    specialize (sLd n).
    specialize (sSt n).
    specialize (bLd n).
    specialize (bSt n).

    unfold getStreamIo, getImIo in *; simpl in *; unfold getStreamIo in *; simpl in *.
    destruct (getStreamTransition (buildIm stm getTransIo 0) n).
    destruct (getStreamTransition (buildIm stm getTransIo 0) n).
    destruct stm; simpl in *.
    destruct (getTransIo s s' t); simpl in *.
    destruct p, p, p, p; simpl in *.
    repeat f_equal.

    specialize (sLd a p d1 d).
    specialize (bLd a p d1 d).
    specialize (sSt a p d1 d).
    specialize (bSt a p d1 d).
    destruct d0.





    induction n.

    unfold getStreamIo, getImIo in *; simpl in *; unfold getStreamIo in *; simpl in *.
    destruct stm; simpl in *.
    destruct (getTransIo s s' t); simpl in *.
    destruct p, p, p, p; simpl in *.
    repeat f_equal.

    specialize (sLd a p d1 d).
    specialize (bLd a p d1 d).
    specialize (sSt a p d1 d).
    specialize (bSt a p d1 d).
    destruct d0.

    assert (H: Some (a,p,d1,Ld,d) = Some (a,p,d1,Ld,d)) by reflexivity.
    specialize (sLd H).

    destruct sLd as [[done nopast] | [cb [tb [ldb [u1 rest]]]]].
    auto.
    assert False by omega; intuition.

    apply (sSt); reflexivity.

    reflexivity.

    assert (Some (a, p, d1, 
    destruct 
    intuition.
    Set Printing All.


Section SaSimulate.
  Variable State: Set.
  Variable Trans: AllTransitions State.
  Variable getTransIo: forall s s',
                         Trans s s' -> option (Addr * Proc * Data * Desc * Data). 

  About buildIm.
  Theorem buildImCorrect n:
    forall s (stm: Stream Trans s),
      getStreamIo getImIo n (buildIm stm getTransIo n initData) = getStreamIo getTransIo n stm.
  Variable stm: Stream Trans initState.
  CoFixpoint buildIm n m: Stream InstantMemory m :=

