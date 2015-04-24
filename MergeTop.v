Require Import SeqConsistency.StoreAtomicity SeqConsistency.FreshNew Caches.Top SeqConsistency.TransitionsNew Caches.Rules SeqConsistency.DataTypes.

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

  Variable pc0: Pc.
  Variable state0: PState.
  Variable rob0: Rob.
  Variable ppc0: Ppc.

  Variable sa1b1: Stream
             (TransAB getSpecIo
                getCacheIo)
             (fun _ : Proc => initSpecState Addr Data pc0 state0 rob0 ppc0,
             initGlobalState).

  Definition cstm := getStreamB sa1b1.


  Variable cacheIsStoreAtomic: @StoreAtomicity Addr Data Proc zero initData
                                               GlobalState Transition initGlobalState cstm
                                               getCacheIo.
  Definition simulateImProof :=
    @actualSimThm Addr Data Proc zero decAddr initData GlobalState
                     Transition initGlobalState cstm getCacheIo
                     (cacheIsStoreAtomic).

  Definition buildIm := @buildIm Addr Data Proc decAddr initData GlobalState Transition
                                 initGlobalState cstm getCacheIo 0.

  Definition buildImSimulate := @buildImSimulate Addr Data Proc zero decAddr initData
                                                 GlobalState Transition initGlobalState
                                                 cstm getCacheIo cacheIsStoreAtomic.

  Definition finalTheorem :=
    @stMatch Addr Data Proc zero decAddr decProc initData Pc PState DeltaPState
             pc0 state0 updSt getDecodeElem getLoadDelta Rob Ppc retire compute
             empty add getLoad issueLoad updLoad commit nextPpc set get rob0 ppc0
             GlobalState initGlobalState Transition getCacheIo sa1b1
             buildIm buildImSimulate.
End Merge.

About finalTheorem.