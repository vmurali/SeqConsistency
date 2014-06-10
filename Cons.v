Require Import DataTypes StoreAtomicity AlwaysEventually.
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
Variable State: Set.
Variable DeltaState: Set.

(* Result of decoding an instruction for both processors *)
Inductive HElem :=
  (* For non mem, simply get the delta state *)
| Nm: DeltaState -> HElem
  (* For load, simply get the address for loading *)
| Load: Addr -> HElem
  (* For store, simply get the address and value for loading *)
| Store: Addr -> Data -> HElem.

(* The history element to be logged for each instruction for both processors *)
Inductive HistElem :=
  (* For non mem, log delta state *)
| Nmh: Pc -> DeltaState -> HistElem
  (* For load, log addr, returned value, and delta state *)
| Loadh: Pc -> Addr -> Data -> DeltaState -> HistElem
  (* For store, log addr, sent value *)
| Storeh: Pc -> Addr -> Data -> HistElem.

(* Describes if transition is local to processor or memory initiated, for speculative
 * processor*)
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

  (* Transitions for a speculative processor. Only 5 of the last 7 matters, the
   * rest are there to occupy space and make everyone mad *)
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

  (* State stored by an atomic processor, for each processor *)
  Record ProcState :=
    { hist: Hist;
      getPc: Pc;
      state: State
    }.

  (* Transitions of an atomic processor with an atomic, monolithic memory. Load/store happens
   * instantaneously. Note that the overall state is a (map for each processor) + memory *)
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
  (* This is to ensure that if the stupid speculating processor is doing stuff with ROB
   * or some such useless work, I don't do any useful work here *)
  | Nothing: forall st m, CorrectSystem st m st m.

  (* State stored by an speculative processor, for each processor *)
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

  (* Transitions of a speculative processor, giving abstracting away the inner transitions
   * and dealing with only abstract Internal and External transitions.
   * Note that overall state is a mapping from each processor *)
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

  (* A co-inductive instantiation of the above transitions to integrate with the previous
   * cache work *)
  CoInductive SpecFinal': (Proc -> SpecState) -> Set :=
  | Build_SF: forall st1 st2, SpecFinal st1 st2 -> SpecFinal' st2 -> SpecFinal' st1.

  (* This whole section contains mainly definitions to finally be able to use the 
   * Store atomicity definition *)
  Section SpecFinal.
    Definition incIs is a p a' p' :=
      match decAddr a a', decProc p p' with
        | left _, left _ => S (is a' p')
        | _, _ => is a' p'
      end.

    (* Getting responses from the co-inductive transitions *)
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

    (* Getting requests in a bad format from the co-inductive transitions *)
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

    (* Getting n^th response from arbitrary co-inductive transitions *)
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

    (* These transitions are the golden transition which will obey StoreAtomicity *)
    Variable spf: SpecFinal' (fun p => spInit).

    (* Getting n^th response from golden transition *)
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

    Definition getSome A (x: option A) (pf: isSome x): A :=
      match x as x0 return match x0 with
                             | Some _ => True
                             | None => False
                           end -> A with
        | Some a => fun _ => a
        | None => fun pf0: False => match pf0 with end
      end pf.

    (* Asserting that the golden transition will always have memory requests *)
    Variable alSpf: forall a p, AlwaysEventually (@isSome _) (getRq spf a p).

    (* Getting the n^th request from the golden transition in bad format *)
    Definition reqFn' a p := getN (@decOption _) (@getSome _) (alSpf a p).

    (* Getting the n^th request from the golden transition in good format *)
    Definition reqFn a p n :=
      match reqFn' a p n with
        | (x, y) => Build_Req x y
      end.

    (* Finally! Asserting that store atomicity holds *)
    Variable isStoreAtomic: StoreAtomicity reqFn respFn.

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

  End SpecFinal.
End PerProc.
