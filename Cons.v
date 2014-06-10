Require Import DataTypes StoreAtomicity AlwaysEventually.
Require Import List Arith.

Set Implicit Arguments.

Definition Tag := nat.

Inductive Rq :=
| LoadCommitRq: Rq
| LoadRq: Tag -> Rq
| StoreRq: Data -> Rq.

Inductive Rp :=
| LoadCommitRp: Data -> Rp
| LoadRp: Tag -> Data -> Rp
| StoreRp: Rp.

Variable Pc: Set.
Variable State: Set.
Variable DeltaState: Set.

Inductive HElem :=
| Nm: DeltaState -> HElem
| Load: Addr -> HElem
| Store: Addr -> Data -> HElem.

Inductive HistElem :=
| Nmh: Pc -> DeltaState -> HistElem
| Loadh: Pc -> Addr -> Data -> DeltaState -> HistElem
| Storeh: Pc -> Addr -> Data -> HistElem.

Inductive TransType := Internal | External.

Section PerProc.
  Variable updSt: State -> DeltaState -> State.
  Variable getHElem: Pc -> State -> (Pc * HElem).
  Variable getLoadDelta: Pc -> State -> Data -> DeltaState.

  Variable Rob Ppc: Set.
  Variable retire compute empty : Rob -> Rob.
  Variable add: Rob -> Pc -> Rob.
  Variable getLoad: Rob -> option (Tag * Addr).
  Variable issueLoad: Rob -> Tag -> Rob.
  Variable updLoad: Rob -> Tag -> Data -> Rob.
  Variable getComPc: Rob -> option Pc.
  Variable commit: Rob -> option (Pc * HistElem).
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

  Definition Hist := list HistElem.

  Inductive Spec:
    Hist -> State -> Pc -> (Addr -> list Rq) -> list Rp -> bool -> Rob -> Ppc ->
    Hist -> State -> Pc -> (Addr -> list Rq) -> list Rp -> bool -> Rob -> Ppc ->
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
  | SpecLoadRq:
      forall h st pc p2m m2p w rob ppc tag a,
        getLoad rob = Some (tag, a) ->
        Spec h st pc p2m m2p w rob ppc
             h st pc (updQ p2m a (LoadRq tag)) m2p w (issueLoad rob tag) ppc
             Internal
  | SpecLoadRp:
      forall h st pc p2m m2p w rob ppc tag v xs,
        m2p = LoadRp tag v :: xs ->
        Spec h st pc p2m m2p w rob ppc
             h st pc p2m xs w (updLoad rob tag v) ppc
             Internal
  | SpecAbort:
      forall h st pc p2m m2p rob ppc pc',
        getComPc rob = Some pc' -> pc' <> pc ->
        Spec h st pc p2m m2p false rob ppc
             h st pc p2m m2p false (empty rob) (set ppc pc)
             Internal
  | SpecComNm:
      forall h st pc p2m m2p rob ppc nextPc delS,
        commit rob = Some (pc, Nmh nextPc delS) ->
        getHElem pc st = (nextPc, Nm delS) ->
        Spec h st pc p2m m2p false rob ppc
             (Nmh pc delS :: h) (updSt st delS) nextPc p2m m2p false rob ppc
             Internal
  | SpecComStRq:
      forall h st pc p2m m2p rob ppc nextPc a v,
        commit rob = Some (pc, Storeh nextPc a v) ->
        getHElem pc st = (nextPc, Store a v) ->
        Spec h st pc p2m m2p false rob ppc
             h st pc (updQ p2m a (StoreRq v)) m2p true rob ppc
             Internal
  | SpecComStRp:
      forall h st pc p2m m2p rob ppc nextPc a v xs,
        commit rob = Some (pc, Storeh nextPc a v) ->
        getHElem pc st = (nextPc, Store a v) ->
        m2p = StoreRp :: xs ->
        Spec h st pc p2m m2p false rob ppc
             (Storeh pc a v :: h) st nextPc p2m xs false rob ppc
             Internal
  | SpecComLoadRq:
      forall h st pc p2m m2p rob ppc nextPc a v delS,
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
        Spec h st pc p2m m2p false rob ppc
             h st pc (updQ p2m a LoadCommitRq) m2p true rob ppc
             Internal
  | SpecComLoadRpGood:
      forall h st pc p2m m2p rob ppc nextPc a v delS xs,
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
        m2p = LoadCommitRp v :: xs ->
        getLoadDelta pc st v = delS ->
        Spec h st pc p2m m2p false rob ppc
             (Loadh pc a v delS :: h) (updSt st delS) nextPc p2m xs false rob ppc
             Internal
  | SpecComLoadRpBad:
      forall h st pc p2m m2p rob ppc nextPc a v delS xs v' delS',
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
        m2p = LoadCommitRp v' :: xs ->
        v <> v' ->
        getLoadDelta pc st v' = delS' ->
        Spec h st pc p2m m2p false rob ppc
             (Loadh pc a v' delS' :: h) (updSt st delS') nextPc p2m xs false
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
  | Lod:
      forall p st m a nextPc delS,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, Load a) ->
        getLoadDelta (getPc (st p)) (state (st p)) (m a) = delS ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Loadh (getPc (st p)) a (m a) delS :: (hist (st p)))
                                      nextPc (updSt (state (st p)) delS))) m
  | Str:
      forall p st m a nextPc v,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, Store a v) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Storeh (getPc (st p)) a v :: (hist (st p)))
                                      nextPc (state (st p)))) (updM m a v)
  | NonMem:
      forall p st m nextPc delS,
        getHElem (getPc (st p)) (state (st p)) = (nextPc, Nm delS) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Nmh (getPc (st p)) delS :: (hist (st p)))
                                      nextPc (updSt (state (st p)) delS))) m
  | Nothing: forall st m, CorrectSystem st m st m.

  Record SpecState :=
    { hist': Hist;
      st: State;
      pc: Pc;
      p2m: Addr -> list Rq;
      m2p: list Rp;
      wait: bool;
      rob: Rob;
      ppc: Ppc
    }.

  Inductive SpecFinal: (Proc -> SpecState) -> (Proc -> SpecState) -> Set :=
  | Int:
      forall state p h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc',
        state p = Build_SpecState h st pc p2m m2p wait rob ppc ->
        Spec h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' Internal ->
        SpecFinal state
                  (updP state p (Build_SpecState h' st' pc' p2m' m2p' wait' rob' ppc'))
  | Ext:
      forall state p h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' a x y,
        state p = Build_SpecState h st pc p2m m2p wait rob ppc ->
        Spec h st pc p2m m2p wait rob ppc
             h' st' pc' p2m' m2p' wait' rob' ppc' External ->
        p2m a = p2m' a ++ (x :: nil) ->
        (forall a', a' <> a -> p2m a = p2m' a) ->
        m2p' = m2p ++ (y :: nil) ->
        SpecFinal state
                  (updP state p (Build_SpecState h' st' pc' p2m' m2p' wait' rob' ppc')).

  CoInductive SpecFinal': (Proc -> SpecState) -> Set :=
  | Build_SF: forall st1 st2, SpecFinal st1 st2 -> SpecFinal' st2 -> SpecFinal' st1.

  Section SpecFinal.
    Definition incIs is a p a' p' :=
      match decAddr a a', decProc p p' with
        | left _, left _ => S (is a' p')
        | _, _ => is a' p'
      end.

    CoFixpoint getRp spa (spf': SpecFinal' spa) (is: Addr -> Proc -> Index) :=
      match spf' with
        | Build_SF _ _ spf future =>
          match spf with
            | Ext _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x y _ _ p2m1 _ m2prel =>
              match y with
                | LoadRp _ v => Cons (Some (a, p, is a p, v)) (getRp future (incIs is a p))
                | LoadCommitRp v => Cons (Some (a, p, is a p, v))
                                         (getRp future (incIs is a p))
                | StRp => Cons (Some (a, p, is a p, initData zero))
                               (getRp future (incIs is a p))
              end
            | Int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              Cons None (getRp future is)
          end
      end.

    CoFixpoint getRq sta (spf': SpecFinal' sta) :=
      match spf' with
        | Build_SF _ _ spf future =>
          match spf with
            | Ext _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x y _ _ p2m1 _ m2prel =>
              match x with
                | LoadRq _ =>
                  fun a' p' =>
                    match decAddr a a', decProc p p' with
                      | left _, left _ => Cons (Some (Ld, initData zero)) (getRq future a' p')
                      | _ , _ => Cons None (getRq future a' p')
                    end
                | LoadCommitRq =>
                  fun a' p' =>
                    match decAddr a a', decProc p p' with
                      | left _, left _ => Cons (Some (Ld, initData zero)) (getRq future a' p')
                      | _ , _ => Cons None (getRq future a' p')
                    end
                | StoreRq v =>
                  fun a' p' =>
                    match decAddr a a', decProc p p' with
                      | left _, left _ => Cons (Some (St, v)) (getRq future a' p')
                      | _ , _ => Cons None (getRq future a' p')
                    end
              end
            | Int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              fun a' p' => Cons None (getRq future a' p')
          end
      end.

    Fixpoint respFn' ls n :=
      match n with
        | 0 => match ls with
                 | Cons (Some (a, p, i, v)) rest =>
                   Some (Build_Resp a p i v)
                 | Cons None rest =>
                   None
               end
        | S m => match ls with
                   | Cons _ rest =>
                     respFn' rest m
                 end
      end.

    Variable initPc: Pc.
    Variable initState: State.
    Variable initRob: Rob.
    Variable initPpc: Ppc.

    Definition normInit := Build_ProcState nil initPc initState.

    Definition spInit := Build_SpecState nil initState initPc (fun a => nil) nil false
                                         initRob initPpc.

    Variable spf: SpecFinal' (fun p => spInit).

    Definition respFn := respFn' (getRp spf (fun a p => 0)).

    Definition isSome A (x: option A) :=
      match x with
        | Some y => True
        | _ => False
      end.

    Theorem decOption A (x: option A): {isSome x} + {~ isSome x}.
    Proof.
      unfold isSome; destruct x; intuition.
    Qed.

    Variable alSpf: forall a p, AlwaysEventually (@isSome _) (getRq spf a p).

    Definition reqFn' a p := getN (@decOption _) (alSpf a p).

    Definition reqFn a p n :=
      match reqFn' a p n with
        | Some (x, y) => Build_Req x y
        | None => Build_Req Ld (initData zero)
      end.

    Variable isStoreAtomic: StoreAtomicity reqFn respFn.

    Inductive CorrectSystemExec: (Proc -> ProcState) -> Mem -> Prop :=
    | CsExec: forall st1 st2 m1 m2, CorrectSystem st1 m1 st2 m2 -> CorrectSystemExec st1 m1 ->
                              CorrectSystemExec st2 m2
    | CsInit: CorrectSystemExec (fun p => normInit) initData.

    Inductive SpecSystemExec: (Proc -> SpecState) -> Prop :=
    | SpExec: forall st1 st2, SpecFinal st1 st2 -> SpecSystemExec st1 ->
                              SpecSystemExec st2
    | SpInit: SpecSystemExec (fun p => spInit).

    Theorem histMatch:
      forall ss, SpecSystemExec ss ->
                 exists ps m, CorrectSystemExec ps m /\
                              forall p, hist (ps p) = hist' (ss p).
    Proof.
      admit.
    Qed.

  End SpecFinal.
End PerProc.
