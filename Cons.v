Require Import DataTypes StoreAtomicity AlwaysEventually AtomicRegIfc AtomicRegThm AtomicReg.
Require Import List Arith.

Set Implicit Arguments.

Definition Tag := nat.

(* Request data type only for speculative processor *)
Inductive Rq :=
| LoadCommitRq: Rq
| LoadRq: Tag -> Rq
| StoreRq: Data -> Rq.

(* Response data type only for speculative processor *)
Inductive Rp :=
| LoadCommitRp: Data -> Rp
| LoadRp: Tag -> Data -> Rp
| StoreRp: Rp.

Variable Pc: Set.
Variable PState: Set.
Variable DeltaPState: Set.

(* Result of decoding an instruction for both processors *)
Inductive DecodeElem :=
  (* For non mem, simply get the delta state *)
| Nm: DeltaPState -> DecodeElem
  (* For load, simply get the address for loading *)
| Load: Addr -> DecodeElem
  (* For store, simply get the address and value for loading *)
| Store: Addr -> Data -> DecodeElem.

(* The history element to be logged for each instruction for both processors *)
Inductive HistElem :=
  (* For non mem, log delta state *)
| Nmh: Pc -> DeltaPState -> HistElem
  (* For load, log addr, returned value, and delta state *)
| Loadh: Pc -> Addr -> Data -> DeltaPState -> HistElem
  (* For store, log addr, sent value *)
| Storeh: Pc -> Addr -> Data -> HistElem.

(* Describes if transition is local to processor or memory initiated, for speculative
 * processor*)
Inductive TransType :=
| Internal: TransType
| External: Rp -> TransType.

Section PerProc.
  Variable updSt: PState -> DeltaPState -> PState.
  Variable getDecodeElem: Pc -> PState -> (Pc * DecodeElem).
  Variable getLoadDelta: Pc -> PState -> Data -> DeltaPState.

  Variable Rob Ppc: Set.
  Variable retire compute empty : Rob -> Rob.
  Variable add: Rob -> Pc -> Rob.
  Variable getLoad: Rob -> option (Tag * Addr).
  Variable issueLoad: Rob -> Tag -> Rob.
  Variable updLoad: Rob -> Tag -> Data -> Rob.
  Variable commit: Rob -> option (Pc * HistElem).
  Variable nextPpc: Ppc -> Ppc.
  Variable set: Ppc -> Pc -> Ppc.
  Variable get: Ppc -> Pc.

  Definition getComPc rob :=
    match commit rob with
      | Some (pc, _) => Some pc
      | None => None
    end.

  Definition updQ A qs idx (v: A) idx' :=
    if decAddr idx idx'
    then  v :: qs idx'
    else qs idx'.

  Definition rmQ A (qs: Addr -> list A) idx idx' :=
    if decAddr idx idx'
    then tail (qs idx')
    else qs idx'.

  Definition Hist := list HistElem.

  (* Transitions for a speculative processor. Only 5 of the last 7 matters, the
   * rest are there to occupy space and make everyone mad *)
  Inductive Spec:
    Hist -> PState -> Pc -> (Addr -> list Rq) -> bool -> Rob -> Ppc ->
    Hist -> PState -> Pc -> (Addr -> list Rq) -> bool -> Rob -> Ppc ->
    TransType -> Prop :=
  | SpecFetch:
      forall h st pc p2m w rob ppc,
        Spec h st pc p2m w rob ppc
             h st pc p2m w (add rob (get ppc)) (nextPpc ppc)
             Internal
  | SpecExec:
      forall h st pc p2m w rob ppc,
        Spec h st pc p2m w rob ppc
             h st pc p2m w (compute rob) ppc
             Internal
  | SpecLoadRq:
      forall h st pc p2m w rob ppc tag a,
        getLoad rob = Some (tag, a) ->
        Spec h st pc p2m w rob ppc
             h st pc (updQ p2m a (LoadRq tag)) w (issueLoad rob tag) ppc
             Internal
  | SpecLoadRp:
      forall h st pc p2m w rob ppc tag v p2m',
        forall a x,
          p2m a = p2m' a ++ x::nil ->
          (forall a', a' <> a -> p2m a' = p2m' a') ->
        Spec h st pc p2m w rob ppc
             h st pc p2m' w (updLoad rob tag v) ppc
             (External (LoadRp tag v))
  | SpecAbort:
      forall h st pc p2m rob ppc pc',
        getComPc rob = Some pc' -> pc' <> pc ->
        Spec h st pc p2m false rob ppc
             h st pc p2m false (empty rob) (set ppc pc)
             Internal
  | SpecComNm:
      forall h st pc p2m rob ppc nextPc delS,
        commit rob = Some (pc, Nmh nextPc delS) ->
        getDecodeElem pc st = (nextPc, Nm delS) ->
        Spec h st pc p2m false rob ppc
             (Nmh pc delS :: h) (updSt st delS) nextPc p2m false (retire rob) ppc
             Internal
  | SpecComStRq:
      forall h st pc p2m rob ppc nextPc a v,
        commit rob = Some (pc, Storeh nextPc a v) ->
        getDecodeElem pc st = (nextPc, Store a v) ->
        Spec h st pc p2m false rob ppc
             h st pc (updQ p2m a (StoreRq v)) true rob ppc
             Internal
  | SpecComStRp:
      forall h st pc p2m rob ppc nextPc a v p2m',
        forall x,
          p2m a = p2m' a ++ x::nil ->
          (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Storeh nextPc a v) ->
        getDecodeElem pc st = (nextPc, Store a v) ->
        Spec h st pc p2m true rob ppc
             (Storeh pc a v :: h) st nextPc p2m' false (retire rob) ppc
             (External StoreRp)
  | SpecComLoadRq:
      forall h st pc p2m rob ppc nextPc a v delS,
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        Spec h st pc p2m false rob ppc
             h st pc (updQ p2m a LoadCommitRq) true rob ppc
             Internal
  | SpecComLoadRpGood:
      forall h st pc p2m rob ppc nextPc a v delS p2m',
        forall x,
          p2m a = p2m' a ++ x::nil ->
          (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        getLoadDelta pc st v = delS ->
        Spec h st pc p2m true rob ppc
             (Loadh pc a v delS :: h) (updSt st delS) nextPc p2m' false (retire rob) ppc
             (External (LoadCommitRp v))
  | SpecComLoadRpBad:
      forall h st pc p2m rob ppc nextPc a v delS v' delS' p2m',
        forall x,
          p2m a = p2m' a ++ x::nil ->
          (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        v <> v' ->
        getLoadDelta pc st v' = delS' ->
        Spec h st pc p2m true rob ppc
             (Loadh pc a v' delS' :: h) (updSt st delS') nextPc p2m' false
             (empty rob) (set ppc nextPc)
             (External (LoadCommitRp v')).

  Definition Mem := Addr -> Data.

  Definition updP A st p (v: A) p' :=
    if decProc p p'
    then v
    else st p'.

  Definition updM A mem a (v: A) a' :=
    if decAddr a a'
    then v
    else mem a'.

  (* PState stored by an atomic processor, for each processor *)
  Record ProcState :=
    { hist: Hist;
      getPc: Pc;
      state: PState
    }.

  (* Transitions of an atomic processor with an atomic, monolithic memory. Load/store happens
   * instantaneously. Note that the overall state is a (map for each processor) + memory *)
  Inductive CorrectSystem: (Proc -> ProcState) -> Mem ->
                             (Proc -> ProcState) -> Mem -> Set :=
  | Lod:
      forall p st m a nextPc delS,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Load a) ->
        getLoadDelta (getPc (st p)) (state (st p)) (m a) = delS ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Loadh (getPc (st p)) a (m a) delS :: (hist (st p)))
                                      nextPc (updSt (state (st p)) delS))) m
  | Str:
      forall p st m a nextPc v,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Store a v) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Storeh (getPc (st p)) a v :: (hist (st p)))
                                      nextPc (state (st p)))) (updM m a v)
  | NonMem:
      forall p st m nextPc delS,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Nm delS) ->
        CorrectSystem
          st m
          (updP st p (Build_ProcState (Nmh (getPc (st p)) delS :: (hist (st p)))
                                      nextPc (updSt (state (st p)) delS))) m
  (* This is to ensure that if the stupid speculating processor is doing stuff with ROB
   * or some such useless work, I don't do any useful work here *)
  | Nothing: forall st m, CorrectSystem st m st m.

  (* PState stored by an speculative processor, for each processor *)
  Record SpecState :=
    { hist': Hist;
      st: PState;
      pc: Pc;
      p2m: Addr -> list Rq;
      wait: bool;
      rob: Rob;
      ppc: Ppc
    }.

  (* Transitions of a speculative processor, giving abstracting away the inner transitions
   * and dealing with only abstract Internal and External transitions.
   * Note that overall state is a mapping from each processor *)
  Inductive SpecFinal: (Proc -> SpecState) -> (Proc -> SpecState) -> Set :=
  | Int:
      forall state p h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc',
        state p = Build_SpecState h st pc p2m wait rob ppc ->
        Spec h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc' Internal ->
        SpecFinal state
                  (updP state p (Build_SpecState h' st' pc' p2m' wait' rob' ppc'))
  | Ext:
      forall state p h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc' a x v,
        state p = Build_SpecState h st pc p2m wait rob ppc ->
        Spec h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc' (External match x with
                                                         | LoadRq t => LoadRp t v
                                                         | LoadCommitRq => LoadCommitRp v
                                                         | StoreRq _ => StoreRp
                                                       end ) ->
        p2m a = p2m' a ++ (x :: nil) ->
        (forall a', a' <> a -> p2m a = p2m' a) ->
        SpecFinal state
                  (updP state p (Build_SpecState h' st' pc' p2m' wait' rob' ppc')).

  Variable initPc: Pc.
  Variable initState: PState.
  Variable initRob: Rob.
  Variable initPpc: Ppc.

  Definition normInit := Build_ProcState nil initPc initState.

  Definition spInit := Build_SpecState nil initState initPc (fun a => nil) false
                                       initRob initPpc.

  (* Defining a transition list for atomic processor atomic memory system *)
  Inductive CorrectSystemExec: (Proc -> ProcState) -> Mem -> Prop :=
  | CsExec: forall st1 st2 m1 m2, CorrectSystem st1 m1 st2 m2 -> CorrectSystemExec st1 m1 ->
                                  CorrectSystemExec st2 m2
  | CsInit: CorrectSystemExec (fun p => normInit) initData.

  (* Defining a transition list for speculative processor *)
  Inductive SpecSystemExec: (Proc -> SpecState) -> Prop :=
  | SpExec: forall st1 st2, SpecFinal st1 st2 -> SpecSystemExec st1 ->
                            SpecSystemExec st2
  | SpInit: SpecSystemExec (fun p => spInit).

  (* Asserting that the histories match *)
  Theorem histMatch:
    forall ss, SpecSystemExec ss ->
               exists ps m, CorrectSystemExec ps m /\
                            forall p, hist (ps p) = hist' (ss p).
  Proof.
    admit.
  Qed.
End PerProc.
