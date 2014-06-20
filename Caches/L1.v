Require Import DataTypes Omega Coq.Logic.Classical MsiState.

Set Implicit Arguments.

Module Type L1Axioms (dt: DataTypes).
  Import dt.
  Axiom deqLeaf: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> leaf c.
  Axiom deqDef: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> defined c.
  Axiom processDeq: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) ->
                                         match w with
                                           | Ld => sle Sh (state c a t)
                                           | St => state c a t = Mo
                                         end.
End L1Axioms.

Module Type L1Theorems (dt: DataTypes) (l1A: L1Axioms dt).
  Import dt l1A.
  Parameter latestValue:
  forall a c t,
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    (data c a t = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi,
                                   ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)) \/
    (exists cb tb, tb < t /\ getStreamCacheIo tb = Some (a, cb, data c a t, St, initData zero) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi,
                     ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)).

  Parameter uniqM:
  forall c a t,
    defined c -> leaf c ->
    state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.

End L1Theorems.
