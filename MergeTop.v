Require Import SeqConsistency.StoreAtomicity SeqConsistency.Fresh Caches.Top SeqConsistency.Transitions Caches.Rules SeqConsistency.DataTypes.

About statesMatchFinal.

Section Merge.
  Definition Addr := Caches.DataTypes.Addr.
  Definition Data := Caches.DataTypes.Data.
  Definition Proc := Caches.DataTypes.Cache.
  Definition zero := Caches.DataTypes.zero.
  Definition decAddr := Caches.DataTypes.decAddr.
  Definition decProc := Caches.Tree.decTree.
  Definition initData := Caches.DataTypes.initData.

  Definition InstantMemory := @InstantMemory Addr Data Proc decAddr initData.
  Definition getImIo := @getImIo Addr Data Proc zero decAddr initData.

  Variable cacheIsStoreAtomic: forall stm,
                                 @StoreAtomicity _ _ _ zero initData
                                                 _ _ initGlobalState stm getCacheIo.
  Definition simulateImProof stm :=
    @actualSimThm Addr Data Proc zero decAddr initData GlobalState
                     Transition initGlobalState stm getCacheIo
                     (cacheIsStoreAtomic stm).

  Variable Pc PState DeltaPState: Set.
  Variable updSt: PState -> DeltaPState -> PState.
  Variable getDecodeElem: Pc -> PState -> (Pc * (DecodeElem Addr Data DeltaPState)).
  Variable getLoadDelta: Pc -> PState -> Data -> DeltaPState.

  Variable Rob Ppc: Set.
  Variable retire compute empty : Rob -> Rob.
  Variable add: Rob -> Pc -> Rob.
  Variable getLoad: Rob -> option (Tag * Addr).
  Variable issueLoad: Rob -> Tag -> Rob.
  Variable updLoad: Rob -> Tag -> Data -> Rob.
  Variable commit: Rob -> option (Pc * (HistElem Addr Data Pc DeltaPState)).
  Variable nextPpc: Ppc -> Ppc.
  Variable set: Ppc -> Pc -> Ppc.
  Variable get: Ppc -> Pc.

  Definition Correct := @Correct Addr Data Proc decProc Pc PState DeltaPState updSt
                                 getDecodeElem getLoadDelta.
  Definition Spec := @Spec Addr Data Proc decAddr decProc Pc PState DeltaPState updSt
                           getDecodeElem getLoadDelta Rob Ppc retire compute empty
                           add getLoad issueLoad updLoad commit nextPpc set get.

  Definition getCorrectIo := @getCorrectIo Addr Data Proc zero decProc initData
                                           Pc PState DeltaPState updSt getDecodeElem
                                           getLoadDelta.
  Definition getSpecIo := @getSpecIo Addr Data Proc zero decAddr decProc initData
                                     Pc PState DeltaPState updSt getDecodeElem
                                     getLoadDelta Rob Ppc retire compute empty
                                     add getLoad issueLoad updLoad commit
                                     nextPpc set get.

  Definition stateA1ToA2 := @stateA1ToA2 Addr Data Proc Pc PState Rob Ppc.
  Definition convertSpecToCorrect := @convertSpecToCorrect Addr Data Proc zero decAddr decProc
                                                           initData Pc PState DeltaPState
                                                           updSt getDecodeElem getLoadDelta Rob
                                                           Ppc retire compute empty add getLoad
                                                           issueLoad updLoad commit
                                                           nextPpc set.

  Definition finalCondition := @finalCondition Addr Data Proc zero decAddr decProc initData Pc
                                               PState DeltaPState updSt getDecodeElem
                                               getLoadDelta Rob Ppc retire compute empty add
                                               getLoad issueLoad
                                               updLoad commit nextPpc set get.

  About statesMatchFinal.
  Definition Io := option (Addr * Proc * Data * Desc * Data).

  Variable decData: forall d1 d2: Data, {d1=d2}+{d1<>d2}.

  Theorem decIo: forall i1 i2: Io, {i1=i2}+{i1 <> i2}.
  Proof.
    intros.
    unfold Io in *.
    decide equality.
    destruct a,p.
    decide equality.
    destruct a,p1.
    decide equality.
    decide equality.
    destruct a,p3.
    decide equality.
    destruct a,p5.
    decide equality.
    apply decTree.
    apply decAddr.
  Qed.

  About statesMatchFinal.
  Definition finalTheorem :=
    statesMatchFinal getCorrectIo getImIo stateA1ToA2 decIo
                     (simulateImProof) convertSpecToCorrect finalCondition.
About SpecState.
About getImIo.

Definition finalTheorem :=
  @statesMatchFinal
    (Proc -> (@SpecState))
    (Proc -> ProcState)
    Caches.Rules.GlobalState
    (Addr -> Data).
    Caches.Rules.getCacheIo
    (@getImIo _ _ _ zer initData)
    stateA1ToA2.
    (Spec decAddr decProc updSt getDecodeElem getLoadDelta retire compute empty
          add getLoad issueLoad updLoad commit nextPpc set get).