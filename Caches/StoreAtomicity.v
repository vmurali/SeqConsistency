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
  Variable getTransIo: forall s s', Trans s s' -> option (Addr * Cache * Data * Desc * Data). 

  Record StoreAtomicity := {
   storeAtomicityLd:
    forall t a c d ld,
      getStreamIo getTransIo t stm = Some (a, c, d, Ld, ld) ->
      (d = initData zero /\ ld = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamIo getTransIo ti stm = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo getTransIo tb stm = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
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

Section AllSa.
  Variable stm: Stream InstantMemory initData.

(*
  Theorem stmSa: StoreAtomicity stm getImIo.
  Proof.
    constructor.

    induction t.
    intros.
*)
End AllSa.