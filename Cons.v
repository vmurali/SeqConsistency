Require Import DataTypes.
Require Import List.

Set Implicit Arguments.

Definition Tag := nat.

Inductive Req :=
| LdCommitReq: Addr -> Req
| LdReq: Tag -> Addr -> Req
| StReq: Addr -> Data -> Req.

Inductive Resp :=
| LdCommitResp: Data -> Resp
| LdResp: Tag -> Data -> Resp
| StResp: Resp.

Inductive Inst :=
| Nm: Inst
| Ld: Addr -> Inst
| St: Addr -> Data -> Inst.

Section PerProc.
  Variable Pc: Set.
  Variable State: Set.
  Variable DeltaState: Set.

  Variable nextSt: Pc -> option Data -> (Pc * Inst * DeltaState).
  Variable updSt: State -> DeltaState -> State.

  Inductive Normal: State -> Pc -> list Req -> list Resp -> bool ->
                    State -> Pc -> list Req -> list Resp -> bool -> Prop :=
  | ComNonMem: forall s nextPc p2m m2p nextPc' delS,
                 nextSt nextPc None = (nextPc', Nm, delS) ->
                 Normal s nextPc p2m m2p false (updSt s delS) nextPc' p2m m2p false
  | ComSt: forall s nextPc p2m m2p nextPc' delS a v,
             nextSt nextPc None = (nextPc', St a v, delS) ->
             Normal s nextPc p2m m2p false (updSt s delS) nextPc' (StReq a v :: p2m) m2p true
  | ComStRp: forall s nextPc p2m m2p,
               Normal s nextPc p2m (StResp :: m2p) true s nextPc p2m m2p false
  | ComLd: forall s nextPc p2m m2p nextPc' delS a,
             nextSt nextPc None = (nextPc', Ld a, delS) ->
             Normal s nextPc p2m m2p false s nextPc (LdCommitReq a :: p2m) m2p true
  | ComLdRp:
      forall s nextPc p2m m2p nextPc' delS a v,
        nextSt nextPc (Some v) = (nextPc', Ld a, delS) ->
        Normal s nextPc p2m (LdCommitResp v :: m2p) true (updSt s delS) nextPc' p2m m2p false
  | ExternalReq:
      forall s nextPc p2m m2p x w,
        Normal s nextPc (p2m ++ (x :: nil)) m2p w s nextPc p2m m2p w
  | ExternalResp:
      forall s nextPc p2m m2p x w,
        Normal s nextPc p2m (m2p ++ (x :: nil)) w s nextPc p2m m2p w.

  Section NormalList.
    Variable s0: State.
    Variable n0: Pc.
    Inductive NormalList:
      State -> Pc -> list Req -> list Resp -> bool -> Prop :=
    | InitNormal: NormalList s0 n0 nil nil false
    | CreateNormal: forall s nextPc p2m m2p w s' nextPc' p2m' m2p' w',
                      Normal s nextPc p2m m2p w s' nextPc' p2m' m2p' w' ->
                      NormalList s nextPc p2m m2p w ->
                      NormalList s' nextPc' p2m' m2p' w'.
  End NormalList.

  Variable Rob: Set.

  Definition CommitEntry := (Pc * Pc * Inst * option Data * DeltaState)%type.

  Variable enq: Pc -> Rob -> Rob.

  Variable Ppc: Set.
  Variable nextPpc: Ppc -> Ppc.
  Variable execute: Rob -> Rob.
  Variable getLoad: Rob -> option (Tag * Addr)%type.
  Variable issueLoad: Tag -> Rob -> Rob.
  Variable updLoad: Tag -> Data -> Rob -> Rob.
  Variable getCommitPc: Rob -> option Pc.
  Variable empty: Rob.
  Variable setPpc: Pc -> Ppc.
  Variable getCommitFull: Rob -> option CommitEntry.
  Variable finishCommit: Rob -> Rob.

  Inductive CommitState :=
  | StCom: CommitState
  | LdCom: Pc -> Addr -> Data -> DeltaState -> CommitState.

  Inductive Spec:
    State -> Pc -> list Req -> list Resp -> Rob ->
    option (CommitState) -> Ppc ->
    State -> Pc -> list Req -> list Resp -> Rob ->
    option (CommitState) -> Ppc -> Set :=
  | SpecNotLd: forall s nextPc p2m m2p rob nextCommit ppc,
                 Spec s nextPc p2m m2p rob nextCommit ppc
                      s nextPc p2m m2p (enq nextPc rob) nextCommit (nextPpc ppc)
  | SpecExecute: forall s nextPc p2m m2p rob nextCommit ppc,
                   Spec s nextPc p2m m2p rob nextCommit ppc
                        s nextPc p2m m2p (execute rob) nextCommit ppc
  | SpecLdReq:
      forall s nextPc p2m m2p rob nextCommit ppc tag a,
        getLoad rob = Some (tag, a) ->
        Spec s nextPc p2m m2p rob nextCommit ppc
             s nextPc (LdReq tag a :: p2m) m2p (issueLoad tag rob) nextCommit ppc
  | SpecLdResp:
      forall s nextPc p2m m2p rob nextCommit ppc tag v,
        Spec s nextPc p2m (LdResp tag v :: m2p) rob nextCommit ppc
             s nextPc p2m m2p (updLoad tag v rob) nextCommit ppc
  | SpecAbort:
      forall s nextPc p2m m2p rob ppc,
        getCommitPc rob <> Some nextPc ->
        Spec s nextPc p2m m2p rob None ppc
             s nextPc p2m m2p empty None (setPpc nextPc)
  | SpecComNm:
      forall s nextPc p2m m2p rob ppc delS nextPc',
        getCommitFull rob = Some (nextPc, nextPc', Nm, None, delS) ->
        nextSt nextPc None = (nextPc', Nm, delS) ->
        Spec s nextPc p2m m2p rob None ppc
             (updSt s delS) nextPc' p2m m2p (finishCommit rob) None ppc
  | SpecComStReq:
      forall s nextPc p2m m2p rob ppc delS nextPc' a v,
        getCommitFull rob = Some (nextPc, nextPc', St a v, None, delS) ->
        nextSt nextPc None = (nextPc', St a v, delS) ->
        Spec s nextPc p2m m2p rob None ppc
             (updSt s delS) nextPc' (StReq a v :: p2m) m2p
             (finishCommit rob) (Some StCom) ppc
  | SpecComStResp:
      forall s nextPc p2m m2p rob ppc,
        Spec s nextPc p2m (StResp :: m2p) rob (Some StCom) ppc
             s nextPc p2m m2p (finishCommit rob) None ppc
  | SpecComLdReq:
      forall s nextPc p2m m2p rob ppc delS nextPc' a v,
        getCommitFull rob = Some (nextPc, nextPc', Ld a, Some v, delS) ->
        Spec s nextPc p2m m2p rob None ppc
             s nextPc (StReq a v :: p2m) m2p
             (finishCommit rob) (Some (LdCom nextPc' a v delS)) ppc
  | SpecComLdRespGood:
      forall s nextPc p2m m2p rob ppc delS nextPc' a v,
        nextSt nextPc (Some v) = (nextPc', Ld a, delS) ->
        Spec s nextPc p2m (LdCommitResp v :: m2p) rob (Some (LdCom nextPc' a v delS)) ppc
             (updSt s delS) nextPc' p2m m2p (finishCommit rob) None ppc
  | SpecComLdRespBad:
      forall s nextPc p2m m2p rob ppc delS nextPc' a v v' delS',
        nextSt nextPc (Some v') = (nextPc', Ld a, delS') ->
        Spec s nextPc p2m (LdCommitResp v' :: m2p) rob (Some (LdCom nextPc' a v delS)) ppc
             (updSt s delS') nextPc' p2m m2p (finishCommit rob) None ppc
  | SpecExternalReq:
      forall s nextPc p2m m2p x rob nextCommit ppc,
        Spec s nextPc (p2m ++ (x :: nil)) m2p rob nextCommit ppc
             s nextPc p2m m2p rob nextCommit ppc
  | SpecExternalResp:
      forall s nextPc p2m m2p x rob nextCommit ppc,
        Spec s nextPc p2m (m2p ++ (x :: nil)) rob nextCommit ppc
             s nextPc p2m m2p rob nextCommit ppc.

  Section SpecList.
    Variable s0: State.
    Variable n0: Pc.
    Variable ppc0: Ppc.
    Inductive SpecList:
      State -> Pc -> list Req -> list Resp -> Rob -> option CommitState -> Ppc -> Prop :=
    | InitSpec: SpecList s0 n0 nil nil empty None ppc0
    | CreateSpec:
        forall s nextPc p2m m2p rob cs ppc s' nextPc' p2m' m2p' rob' cs' ppc',
          Spec s nextPc p2m m2p rob cs ppc s' nextPc' p2m' m2p' rob' cs' ppc' ->
          SpecList s nextPc p2m m2p rob cs ppc ->
          SpecList s' nextPc' p2m' m2p' rob' cs' ppc'.
  End SpecList.

  Theorem specNormal:
    forall s0 n0 ppc0 s nextPc p2m m2p rob cs ppc,
      SpecList s0 n0 ppc0 s nextPc p2m m2p rob cs ppc ->
      exists p2m' m2p' w,
        NormalList s0 n0 s nextPc p2m' m2p' w.
  Proof.
    admit.
  Qed.
End PerProc.