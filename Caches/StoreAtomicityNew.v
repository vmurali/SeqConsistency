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

  Fixpoint getNStateForStm n :=
    match n with
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

  Program Definition getNTransForStm n:
    InstantMemory (getNStateForStm n) (getNStateForStm (S n)) :=
    match getStreamIo getTransIo n stm as io
          return match io with
                   | Some (a, c, d, w, ld) => InstantMemory (getNStateForStm n)

with
      | Some (a, c, d, w, ld) => IReq (getNStateForStm n) a c d w
      | None => IIdle (getNStateForStm n)
    end.

  Print getNTransForStm.

  Print Stream.
  Program CoFixpoint buildIm n: Stream InstantMemory (getNStateForStm n) :=
    TCons (getNStateForStm n)
          (match getStreamIo getTransIo n stm
             with
               | Some (a, c, d, w, ld) => IReq (getNStateForStm n) a c d w
               | None => IIdle (getNStateForStm n)
             end) (eq_rect_r _ (buildIm (S n)) _).

  Next Obligation.
    admit.
  Qed.
  Next Obligation.
    destruct (getStreamIo getTransIo n stm).
    destruct p3, p3, p3, p3.
    induction n.
    simpl in *.
    unfold getNStateForStm.

  TCons _ (match getStreamIo getTransIo n stm as use
              return (InstantMemory m match use with
                                        | Some (a, _, d, w, _) => if w
                                                                  then m
                                                                  else fun a' =>
                                                                         if decAddr a a'
                                                                         then d
                                                                         else m a'
                                        | None => m
                                      end) with
             | Some (a, c, d, w, ld) => (IReq m a c d w)
             | None => (IIdle m)
           end) (buildIm (S n) (match getStreamIo getTransIo n stm as use
                                   return (Addr -> Data) with
                                  | Some (a, c, d, w, ld) => if w
                                                             then m
                                                             else fun a' =>
                                                                    if decAddr a a'
                                                                    then d
                                                                    else m a'
                                  | None => m
                                end)).

  Theorem distrBuildIm n:
    forall m mem,
      getStreamIo getImIo n (buildIm m mem) = getStreamIo getImIo 0 (buildIm (n+m) mem).
  Proof.
    induction n.
    intros.
    assert (0+m = m) by omega.
    rewrite H.
    reflexivity.
    intros.
    simpl.
    unfold getStreamIo at 1.
    unfold getImIo at 1.
    unfold getStreamTransition at 1.
    simpl.
    
    unfold getStreamIo at 5.
    unfold buildIm
    simpl in *.
    assert (S m + n = m + S n) by omega.
    unfold getStreamIo in IHn at 1.
    simpl in *.
    specialize (IHn (S m)).
    rewrite <- H in *.
    simpl in *.
    destruct (getStreamIo getTransIo n stm).
    unfold buildIm in IHn at 3.
    simpl.
    simpl.
End CreateInstantMemory.

Section AllSa.

  Lemma memVal
        s s' (t: InstantMemory s s') (stm: Stream InstantMemory s'):
    match t with
      | IReq a p d w => if w
                        then forall a', s' a' = s a'
                        else s' a = d
      | IIdle => forall a, s' a = s a
    end.
  Proof.    rewrite <- H in *.

    destruct t.
    destruct w.
    intuition.
    destruct (decAddr a a); intuition.
    intuition.
  Qed.

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

