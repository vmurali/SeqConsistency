Require Import DataTypes.

Set Implicit Arguments.

Section StoreAtomicity.
  Variable getStreamIo: Time -> option (Addr * Cache * Data * Desc * Data).

  Record StoreAtomicity := {
   storeAtomicityLd:
    forall a c d ld t,
      getStreamIo t = Some (a, c, d, Ld, ld) ->
      (d = initData zero /\ ld = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamIo ti = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamIo tb = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                     ~ getStreamIo ti = Some (a, ci, di, St, ldi));

   storeAtomicitySt:
   forall a c d ld t,
     getStreamIo t = Some (a, c, d, St, ld) ->
     ld = initData zero}.
End StoreAtomicity.
