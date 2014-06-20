Require Import DataTypes L1 StoreAtomicity LatestValue Cache Channel Compatible
Rules ChannelAxiom L1Axioms CompatBehavior LatestValueAxioms BehaviorAxioms MsiState.

Set Implicit Arguments.
  Module l1 := mkL1Axioms.
  Module ch' := mkChannel.
  Module ch := mkChannelPerAddr mkDataTypes ch'.
  Module comp := mkCompatBehavior ch.
  Module lv := mkLatestValueAxioms ch.
  Module ba := mkBehaviorAxioms.
  Module l1T := LatestValueTheorems mkDataTypes ch ba l1 comp lv.
    Import mkDataTypes l1 l1T lv.


  Theorem storeAtomicityLd':
    forall a c d ld t,
      getStreamCacheIo t = Some (a, c, d, Ld, ld) ->
      (d = initData zero /\ ld = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi, defined ci ->
                                   ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, defined cb /\ tb < t /\ getStreamCacheIo tb = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi, defined ci ->
                     ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)).
  Proof.
    intros.
    pose proof (deqLeaf H) as lf.
    pose proof (deqDef H) as def.
    pose proof (latestValue a t def lf) as lv.
    pose proof (processDeq H) as sth.
    Opaque sle.
    simpl in *.
    pose proof (deqLdImpData def H) as [u1 u2].
    rewrite <- u2, u1 in *.
    specialize (lv sth).
    intuition.
    right.
    destruct H0 as [cb [tb rest]].
    exists cb, tb, (initData zero).
    assumption.
  Qed.

  Theorem storeAtomicitySt':
    forall a c d ld t,
      getStreamCacheIo t = Some (a, c, d, St, ld) ->
      ld = initData zero.
  Proof.
    intros.
    pose proof (deqLeaf H) as lf.
    pose proof (deqDef H) as def.
    pose proof (deqImpData def H) as [u1 u2].
    assumption.
  Qed.

  Definition cacheIsStoreAtomic := Build_StoreAtomicity getStreamCacheIo storeAtomicityLd' storeAtomicitySt'.
