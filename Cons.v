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
Inductive HElem :=
  (* For non mem, simply get the delta state *)
| Nm: DeltaPState -> HElem
  (* For load, simply get the address for loading *)
| Load: Addr -> HElem
  (* For store, simply get the address and value for loading *)
| Store: Addr -> Data -> HElem.

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
  Variable getHElem: Pc -> PState -> (Pc * HElem).
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
      forall h st pc p2m w rob ppc tag v,
        Spec h st pc p2m w rob ppc
             h st pc p2m w (updLoad rob tag v) ppc
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
        getHElem pc st = (nextPc, Nm delS) ->
        Spec h st pc p2m false rob ppc
             (Nmh pc delS :: h) (updSt st delS) nextPc p2m false rob ppc
             Internal
  | SpecComStRq:
      forall h st pc p2m rob ppc nextPc a v,
        commit rob = Some (pc, Storeh nextPc a v) ->
        getHElem pc st = (nextPc, Store a v) ->
        Spec h st pc p2m false rob ppc
             h st pc (updQ p2m a (StoreRq v)) true rob ppc
             Internal
  | SpecComStRp:
      forall h st pc p2m rob ppc nextPc a v p2m',
        commit rob = Some (pc, Storeh nextPc a v) ->
        getHElem pc st = (nextPc, Store a v) ->
        Spec h st pc p2m true rob ppc
             (Storeh pc a v :: h) st nextPc p2m' false rob ppc
             (External StoreRp)
  | SpecComLoadRq:
      forall h st pc p2m rob ppc nextPc a v delS,
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
        Spec h st pc p2m false rob ppc
             h st pc (updQ p2m a LoadCommitRq) true rob ppc
             Internal
  | SpecComLoadRpGood:
      forall h st pc p2m rob ppc nextPc a v delS p2m',
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
        getLoadDelta pc st v = delS ->
        Spec h st pc p2m true rob ppc
             (Loadh pc a v delS :: h) (updSt st delS) nextPc p2m' false rob ppc
             (External (LoadCommitRp v))
  | SpecComLoadRpBad:
      forall h st pc p2m rob ppc nextPc a v delS v' delS' p2m',
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getHElem pc st = (nextPc, Load a) ->
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

  (* A co-inductive instantiation of the above transitions to integrate with the previous
   * cache work *)
  CoInductive SpecFinalStream: (Proc -> SpecState) -> Set :=
  | Build_SF: forall st1 st2, SpecFinal st1 st2 -> SpecFinalStream st2 -> SpecFinalStream st1.

  (* This whole section contains mainly definitions to finally be able to use the 
   * Store atomicity definition *)
  Section SpecFinal.
    Definition incIs is a p a' p' :=
      match decAddr a a', decProc p p' with
        | left _, left _ => S (is a' p')
        | _, _ => is a' p'
      end.

    (* Getting responses from the co-inductive transitions *)
    CoFixpoint getRp spa (spf': SpecFinalStream spa) (is: Addr -> Proc -> Index) :=
      match spf' with
        | Build_SF _ _ spf future =>
          match spf with
            | Ext _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x v _ _ _ _ =>
              match x with
                | LoadRq t => Cons (Some (a, p, is a p, v)) (getRp future (incIs is a p))
                | LoadCommitRq => Cons (Some (a, p, is a p, v))
                                         (getRp future (incIs is a p))
                | StoreRq _ => Cons (Some (a, p, is a p, initData zero))
                                    (getRp future (incIs is a p))
              end
            | Int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                Cons None (getRp future is)
          end
      end.

    (* Getting requests in a bad format from the co-inductive transitions *)
    CoFixpoint getRq sta (spf': SpecFinalStream sta) :=
      match spf' with
        | Build_SF _ _ spf future =>
          match spf with
            | Ext _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x y _ _ _ _ =>
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
            | Int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
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
    Variable initState: PState.
    Variable initRob: Rob.
    Variable initPpc: Ppc.

    Definition normInit := Build_ProcState nil initPc initState.

    Definition spInit := Build_SpecState nil initState initPc (fun a => nil) false
                                         initRob initPpc.

    (* These transitions are the golden transition which will obey StoreAtomicity *)
    Variable spf: SpecFinalStream (fun p => spInit).

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

    Definition atBeh := atomicBeh (saBehAtomicReg isStoreAtomic).
    Definition atMatch := respMatch (saBehAtomicReg isStoreAtomic).

    (* Speculative system with atomic register *)
    Inductive SpecFinal': (Proc -> SpecState) -> State -> (Proc -> SpecState) -> State -> Set :=
    | Int':
      forall state astate p h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc',
        state p = Build_SpecState h st pc p2m wait rob ppc ->
        Spec h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc' Internal ->
        SpecFinal' state astate
                   (updP state p (Build_SpecState h' st' pc' p2m' wait' rob' ppc')) astate
    | Ext':
      forall state astate p h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc' a x,
        state p = Build_SpecState h st pc p2m wait rob ppc ->
        Spec h st pc p2m wait rob ppc
             h' st' pc' p2m' wait' rob' ppc'
             (External
                match x with
                  | LoadRq t => LoadRp t (mem astate a)
                  | LoadCommitRq => LoadCommitRp (mem astate a)
                  | StoreRq _ => StoreRp
                end) ->
        p2m a = p2m' a ++ (x :: nil) ->
        (forall a', a' <> a -> p2m a = p2m' a) ->
        SpecFinal' state astate
                   (updP state p (Build_SpecState h' st' pc' p2m' wait' rob' ppc'))
                   (Build_State
                      (match x with
                         | StoreRq v => fun a' =>
                                          if decAddr a a'
                                          then v
                                          else mem astate a'
                         | _ => mem astate
                       end)
                      (fun a' t => 
                         if decAddr a a'
                         then
                           match decProc t p with
                             | left _ => S (next astate a' t)
                             | _ => next astate a' t
                           end
                         else next astate a' t
                   )).

    (* A co-inductive instantiation of the above transitions *)
    CoInductive SpecFinalStream': (Proc -> SpecState) -> State -> Set :=
              | Build_SF':
                forall st1 st2 m1 m2,
                  SpecFinal' st1 m1 st2 m2 ->
                  SpecFinalStream' st2 m2 -> SpecFinalStream' st1 m1.

    Definition specFinal'Resp st1 m1 st2 m2 (t: SpecFinal' st1 m1 st2 m2) :=
      match t with
        | Ext' _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x _ _ _ _ => Some
            match x with
              | StoreRq v => Build_Resp a p (next m1 a p) (initData zero)
              | _ => Build_Resp a p (next m1 a p) (mem m1 a)
            end
        | _ => None
      end.

    Fixpoint getResp n s m (al: SpecFinalStream' s m) :=
      match n with
      | 0 => match al with
               | Build_SF' _ _ _ _ f _ => specFinal'Resp f
             end
      | S m => match al with
                 | Build_SF' _ _ _ _ _ al' => getResp m al'
               end
    end.

(*

Some junk. Do not read.

    Require Import JMeq.

    Program CoFixpoint spf' n m s (ss: SpecFinalStream s) :=
    match ss with
      | Build_SF _ _ t ss1 =>
          match t with
            | Int s p _ _ _ _ _ _ _ _ _ _ _ _ _ _ pSt t =>
                Build_SF' (Int' s m p pSt t) (spf' (S n) m ss1)
            | Ext s p _ _ _ _ _ _ _ _ _ _ _ _ _ _ a x v pSt t p2m1 p2m2 =>
                Build_SF' (Ext' s m p x pSt t p2m1 p2m2) (spf' (S n)
                                                               (Build_State
                                                                  (match x with
                                                                     | StoreRq v => fun a' =>
                                                                                      if decAddr a a'
                                                                                      then v
                                                                                      else mem m a'
                                                                     | _ => mem m
                                                                   end)
                                                                  (fun a' t => 
                                                                     if decAddr a a'
                                                                     then
                                                                       match decProc t p with
                                                                         | left _ => S (next m a' t)
                                                                         | _ => next m a' t
                                                                       end
                                                                     else next m a' t
                                                               )) ss1)

          end
    end.

    Next Obligation.
      pose atBeh as abeh.
      unfold atBeh in *.
      pose proof (atMatch n) as atMatch.
      unfold saBehAtomicReg in abeh; simpl in *.
      unfold buildAl in abeh.
      induction n.
      simpl in *.
      unfold atomicResp in *.
      unfold NamedTrans.getTrans in *.
      unfold getTransNext in *.
      simpl in *.
      destruct (respFn 0).
      simpl in *.
      unfold saBehAtomic
      unfold atomicResp in *.
      unfold atomicBeh in H.
      unfold AtomicReg.getResp in H.
      simpl in H.
      
      unfold AtomicReg.atomicResp in *.
      unfold saBehAtomic
      unfold AtomicReg.getResp in *.
      induction 
      
      Proof.
      pose 
      apply (Ext').

    CoFixpoint buildAl n: SpecFinalStream' (lSt (getTransList getTransNext n))
    := TCons (getTrans getTransNext n) (buildAl (S n)).

  Lemma getRespEq' n: forall m, getResp n (buildAl m) = getAtomicResp (n + m).
  Proof.
    unfold getAtomicResp.
    induction n.
    simpl.
    reflexivity.
    intros.
    simpl.
    specialize (IHn (S m)).

    assert (eq: n + S m = S (n + m)) by omega.
    rewrite eq in *.
    intuition.
  Qed.

  Lemma getRespEq n: getResp n (buildAl 0) = getAtomicResp n.
  Proof.
    pose proof (getRespEq' n 0) as sth.
    assert (eq: n+0 = n) by omega.
    rewrite eq in *.
    intuition.
  Qed.

  Theorem storeAtomicityImpAtomicRegBehavior n :
    exists (al: AtomicTransList reqFn (Build_State (initData) (fun a t => 0))),
      respFn n = getResp n al.
  Proof.
    exists (buildAl reqFn respFn 0).
    About getRespEq.
    pose proof (getRespEq sa n) as e1.
    pose proof (respEq sa n) as e2.
    rewrite <- e1 in e2.
    assumption.
  Qed.
*)


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
