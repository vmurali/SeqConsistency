Require Import DataTypes Transitions.

Set Implicit Arguments.

Section StoreAtomicity.
  Variable State: Set.
  Variable Trans: AllTransitions State.
  Variable initState: State.
  Variable stm: Stream Trans initState.
  Variable getTransIo: forall s s', Trans s s' -> option (Addr * Cache * Data * Desc * Data). 

  Record StoreAtomicity := {
   storeAtomicityLd:
    forall a c d ld t,
      getStreamIo getTransIo t stm = Some (a, c, d, Ld, ld) ->
      (d = initData zero /\ ld = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamIo getTransIo ti stm = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo getTransIo tb stm = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                     ~ getStreamIo getTransIo ti stm = Some (a, ci, di, St, ldi));

   storeAtomicitySt:
   forall a c d ld t,
     getStreamIo getTransIo t stm = Some (a, c, d, St, ld) ->
     ld = initData zero}.
End StoreAtomicity.
