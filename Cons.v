Require Import DataTypes.
Require Import List.

Set Implicit Arguments.

Definition Tag := nat.

Inductive Req :=
| LdCommitReq: Req
| LdReq: Tag -> Req
| StReq: Data -> Req.

Inductive Resp :=
| LdCommitResp: Data -> Resp
| LdResp: Tag -> Data -> Resp
| StResp: Resp.

Variable Pc: Set.
Variable State: Set.
Variable DeltaState: Set.

Inductive HElem :=
| Nm: DeltaState -> HElem
| Ld: Addr -> HElem
| St: Addr -> Data -> HElem.

Inductive HistElem :=
| Nmh: DeltaState -> HistElem
| Ldh: Addr -> Data -> DeltaState -> HistElem
| Sth: Addr -> Data -> HistElem.

Definition Hist := list (Pc * HistElem).

Inductive TransType := Internal | External.

Section PerProc.
  Variable updSt: State -> DeltaState -> State.
  Variable getHElem: Pc -> State -> (Pc * HElem).
  Variable getLoadDelta: Pc -> State -> Data -> DeltaState.

  Variable Rob Ppc: Set.
  Variable retire compute empty : Rob -> Rob.
  Variable add: Rob -> Pc -> Rob.
  Variable getLd: Rob -> option (Tag * Addr).
  Variable issueLd: Rob -> Tag -> Rob.
  Variable updLd: Rob -> Tag -> Data -> Rob.
  Variable getComPc: Rob -> option Pc.
  Variable commit: Rob -> option (Pc * Pc * HistElem).
  Variable next: Ppc -> Ppc.
  Variable set: Ppc -> Pc -> Ppc.
  Variable get: Ppc -> Pc.

  Definition updQ A qs idx (v: A) idx' :=
    if decAddr idx idx'
    then  v :: qs idx'
    else qs idx'.

  Definition rmQ A (qs: Addr -> list A) idx idx' :=
    if decAddr idx idx'
    then tail (qs idx')
    else qs idx'.

  Inductive Spec:
    Hist -> State -> Pc -> (Addr -> list Req) -> list Resp -> bool -> Rob -> Ppc ->
    Hist -> State -> Pc -> (Addr -> list Req) -> list Resp -> bool -> Rob -> Ppc ->
    TransType -> Prop :=
  | SpecFetch:
      forall h st pc p2m m2p w rob ppc,
        Spec h st pc p2m m2p w rob ppc
             h st pc p2m m2p w (add rob (get ppc)) (next ppc)
             Internal
  | SpecExec:
      forall h st pc p2m m2p w rob ppc,
        Spec h st pc p2m m2p w rob ppc
             h st pc p2m m2p w (compute rob) ppc
             Internal
  | SpecLdRq:
      forall h st pc p2m m2p w rob ppc tag a,
        getLd rob = Some (tag, a) ->
        Spec h st pc p2m m2p w rob ppc
             h st pc (updQ p2m a (LdReq tag)) m2p w (issueLd rob tag) ppc
             Internal
  | SpecLdRp:
      forall h st pc p2m m2p w rob ppc tag v xs,
        m2p = LdResp tag v :: xs ->
        Spec h st pc p2m m2p w rob ppc
             h st pc p2m xs w (updLd rob tag v) ppc
             Internal
  | SpecAbort:
      forall h st pc p2m m2p rob ppc pc',
        getComPc rob = Some pc' -> pc' <> pc ->
        Spec h st pc p2m m2p false rob ppc
             h st pc p2m m2p false (empty rob) (set ppc pc)
             Internal
  | SpecComNm:
      forall h st pc p2m m2p rob ppc nextPc delS,
        commit rob = Some (pc, nextPc, Nmh delS) ->
        getHElem pc st = (nextPc, Nm delS) ->
        Spec h st pc p2m m2p false rob ppc
             ((pc, Nmh delS) :: h) (updSt st delS) nextPc p2m m2p false rob ppc
             Internal
  | SpecComStRq:
      forall h st pc p2m m2p rob ppc nextPc a v,
        commit rob = Some (pc, nextPc, Sth a v) ->
        getHElem pc st = (nextPc, St a v) ->
        Spec h st pc p2m m2p false rob ppc
             h st pc (updQ p2m a (StReq v)) m2p true rob ppc
             Internal
  | SpecComStRp:
      forall h st pc p2m m2p rob ppc nextPc a v xs,
        commit rob = Some (pc, nextPc, Sth a v) ->
        getHElem pc st = (nextPc, St a v) ->
        m2p = StResp :: xs ->
        Spec h st pc p2m m2p false rob ppc
             ((pc, Sth a v) :: h) st nextPc p2m xs false rob ppc
             Internal
  | SpecComLdRq:
      forall h st pc p2m m2p rob ppc nextPc a v delS,
        commit rob = Some (pc, nextPc, Ldh a v delS) ->
        getHElem pc st = (nextPc, Ld a) ->
        Spec h st pc p2m m2p false rob ppc
             h st pc (updQ p2m a LdCommitReq) m2p true rob ppc
             Internal
  | SpecComLdRpGood:
      forall h st pc p2m m2p rob ppc nextPc a v delS xs,
        commit rob = Some (pc, nextPc, Ldh a v delS) ->
        getHElem pc st = (nextPc, Ld a) ->
        m2p = LdCommitResp v :: xs ->
        getLoadDelta pc st v = delS ->
        Spec h st pc p2m m2p false rob ppc
             ((pc, Ldh a v delS) :: h) (updSt st delS) nextPc p2m xs false rob ppc
             Internal
  | SpecComLdRpBad:
      forall h st pc p2m m2p rob ppc nextPc a v delS xs v' delS',
        commit rob = Some (pc, nextPc, Ldh a v delS) ->
        getHElem pc st = (nextPc, Ld a) ->
        m2p = LdCommitResp v' :: xs ->
        v <> v' ->
        getLoadDelta pc st v' = delS' ->
        Spec h st pc p2m m2p false rob ppc
             ((pc, Ldh a v' delS') :: h) (updSt st delS') nextPc p2m xs false
             (empty rob) (set ppc nextPc)
             Internal
  | SpecMemDeqs:
      forall h st pc p2m m2p w rob ppc p2m' m2p',
        Spec h st pc p2m m2p w rob ppc
             h st pc p2m' m2p' w rob ppc
             External.

  Definition Mem := Addr -> Data.

  Definition updP A st p (v: A) p' :=
    if decProc p p'
    then v
    else st p'.

  Definition updM A mem a (v: A) a' :=
    if decAddr a a'
    then v
    else mem a'.

  Record ProcState :=
    { hist: Hist;
      getPc: Pc;
      state: State
    }.

  Inductive CorrectSystem: (Proc -> ProcState) -> Mem ->
                           (Proc -> ProcState) -> Mem -> Set :=
  | Load:
      forall p st m a nextPc delS,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, Ld a) ->
        getLoadDelta (getPc (st p)) (state (st p)) (m a) = delS ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState ((getPc (st p), Ldh a (m a) delS) :: hist (st p))
                                      nextPc (updSt (state (st p)) delS))) m
  | Store:
      forall p st m a nextPc v,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, St a v) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState ((getPc (st p), Sth a v) :: hist (st p))
                                      nextPc (state (st p)))) (updM m a v)
  | NonMem:
      forall p st m nextPc delS,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, Nm delS) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState ((getPc (st p), Nmh delS) :: hist (st p))
                                      nextPc (updSt (state (st p)) delS))) m.

  Variable initPc: Pc.
  Variable initState: State.
  Variable initRob: Rob.
  Variable initPpc: Ppc.

  Record SpecState :=
    { hist': Hist;
      st: State;
      pc: Pc;
      p2m: Addr -> list Req;
      m2p: list Resp;
      wait: bool;
      rob: Rob;
      ppc: Ppc
    }.

  CoInductive SpecFinal: (Proc -> SpecState) -> Set :=
  | Int:
      forall state p h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc',
        state p = Build_SpecState h st pc p2m m2p wait rob ppc ->
        Spec h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' Internal ->
        SpecFinal (updP state p (Build_SpecState h' st' pc' p2m' m2p' wait' rob' ppc')) ->
        SpecFinal state
  | Ext:
      forall state p h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' a x y,
        state p = Build_SpecState h st pc p2m m2p wait rob ppc ->
        Spec h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' External ->
        p2m a = p2m' a ++ (x :: nil) ->
        (forall a', a' <> a -> p2m a = p2m' a) ->
        m2p' = m2p ++ (y :: nil) ->
        SpecFinal (updP state p (Build_SpecState h' st' pc' p2m' m2p' wait' rob' ppc')) ->
        SpecFinal state.

  About Int.

  CoFixpoint getReq sta :=
    match sta with
      | Ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x y _ _ p2m1 p2m2 m2prel future => None
      | Int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ future => None
    end.
End PerProc.