Require Import DataTypes Transitions.

Set Implicit Arguments.

Inductive InstantMemory : (Addr -> Data) -> (Addr -> Data) -> Set :=
| IReq m a (p: Proc) d (w: Desc):
  InstantMemory m (if w
                   then m
                   else 
                     fun a' => 
                       if decAddr a a'
                       then d
                       else m a')
| IIdle m: InstantMemory m m.

Definition getImIo s s' (t: InstantMemory s s') :=
  match t with
    | IReq m a p d w => Some (a, p, d, w, if w
                                          then m a
                                          else initData zero)
    | IIdle m => None
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
     ld = initData zero}.

  CoFixpoint buildIm n m: Stream InstantMemory m :=
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
End CreateInstantMemory.

(*
Section AllSa.

  Theorem memGood t:
    forall s (stm: Stream InstantMemory s) a,
      (fst (getStreamState t stm) a = s a /\
                        forall ti, 0 <= ti < t ->
                                   forall ci di ldi, defined ci ->
                                                     ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)) \/
      (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo getImIo tb stm =
                         Some (a, cb, fst (getStreamState t stm) a, St, ldb) /\
        forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                                     ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)).
  Proof.
    induction t.
    intros.
    simpl in *.
    destruct stm; simpl.
    constructor; (reflexivity || intuition; assert False by omega; intuition).

    intros.

    simpl in *.
    destruct stm; simpl.

    specialize (IHt _ stm a).
    destruct i; simpl in *.
    destruct w.

    destruct IHt.

    left.
    constructor.
    intuition.

    destruct H as [u1 u2].
    intros.
    
    intros.

    specialize (IHt a).
    destruct IHt.
    constructor.
    constructor.
    specialize (IHt a); intuition.
    

    specialize (IHt a).
    destruct (decAddr a0 a).
    rewrite e in *.

    simpl in *.

        getStreamIo getImIo t stm = Some (a, c, d, Ld, ld) -> Some (a, ci, di, St, ldi)
      (ld = mem a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo getImIo tb stm = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                     ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)).
  Proof.


  Theorem storeAtomicityLd' t:
    forall mem (stm: Stream InstantMemory mem) a c d ld,
      getStreamIo getImIo t stm = Some (a, c, d, Ld, ld) ->
      (ld = mem a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo getImIo tb stm = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                     ~ getStreamIo getImIo ti stm = Some (a, ci, di, St, ldi)).
  Proof.
    induction t.
    intros.

    unfold getStreamIo, getImIo in *.
    simpl in *.
    destruct stm.
    destruct i.
    destruct w.
    injection H; intros.
    rewrite H3, H2, H1, H0 in *.
    left.
    constructor; intuition.
    discriminate.
    discriminate.

    intros.
    unfold getStreamIo, getImIo in *.
    simpl in *.

    destruct stm.
    specialize (IHt s' stm a c d ld H).
    unfold getStream
    injection H; intros.
    assert (sth: fst (getStreamState 0 stm) = initData).
    simpl.
    destruct stm.
    reflexivity.
    destruct stm.
    unfold getImIo in *.
    destruct i.
    destruct w.
    injection H; intros.
    rewrite H3, H2, H1, H0 in *.
    simpl.
    simpl.
    destruct stm.
    unfold getStreamS
    assert (fst (match stm with
                   | TCons s0 s' _ _ => (s0, s'
    destruct stm.
    simpl.
End AllSa.
*)
