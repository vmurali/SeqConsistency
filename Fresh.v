Require Import DataTypes Useful List Coq.Logic.FunctionalExtensionality Transitions.

Set Implicit Arguments.

Inductive InstantMemory m : (Addr -> Data) -> Set :=
| IReq a (p: Proc) d (w: Desc):
  InstantMemory m (if w
                   then m
                   else 
                     fun a' => 
                       if decAddr a a'
                       then d
                       else m a')
| IIdle: InstantMemory m m.

Definition getImIo s s' (t: InstantMemory s s') :=
  match t with
    | IReq a p d w => Some (a, p, d, w, if w
                                          then s a
                                          else initData zero)
    | IIdle => None
  end.


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

Record ProcState :=
  { getPc: Pc;
    state: PState
  }.

Definition upd A (st: Proc -> A) p v p' :=
  match decProc p p' with
    | left _ => v
    | _ => st p'
  end.

Definition updM A mem a (v: A) a' :=
  if decAddr a a'
  then v
  else mem a'.

Section PerProc.
  Variable updSt: PState -> DeltaPState -> PState.
  Variable getDecodeElem: Pc -> PState -> (Pc * DecodeElem).
  Variable getLoadDelta: Pc -> PState -> Data -> DeltaPState.

  (* Transitions of an atomic processor with an atomic, monolithic memory. Load/store happens
   * instantaneously. Note that the overall state is a (map for each processor) + memory *)
  Inductive Correct: (Proc -> ProcState) ->
                     (Proc -> ProcState) -> Set :=
  | Lod:
      forall p st a nextPc delS v,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Load a) ->
        getLoadDelta (getPc (st p)) (state (st p)) v = delS ->
        Correct
          st (upd st p (Build_ProcState nextPc (updSt (state (st p)) delS)))
  | Str:
      forall p st a nextPc v,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Store a v) ->
        Correct
          st
          (upd st p (Build_ProcState nextPc (state (st p))))
  | NonMem:
      forall p st nextPc delS,
        getDecodeElem (getPc (st p)) (state (st p)) = (nextPc, Nm delS) ->
        Correct
          st
          (upd st p (Build_ProcState nextPc (updSt (state (st p)) delS)))
  | Nothing: forall st, Correct st st.

  Definition getCorrectIo s s' (t: Correct s s') :=
    match t with
      | Lod p _ a _ _ v _ _ => Some (a, p, initData zero, Ld, v)
      | Str p _ a _ v _ => Some (a, p, v, St, initData zero)
      | NonMem p _ _ _ _ => None
      | Nothing _ => None
    end.

  Inductive HistElem :=
  | Nmh: Pc -> DeltaPState -> HistElem
  | Loadh: Pc -> Addr -> Data -> DeltaPState -> HistElem
  | Storeh: Pc -> Addr -> Data -> HistElem.

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

  (* PState stored by an speculative processor, for each processor *)
  Record SpecState :=
    { st: PState;
      pc: Pc;
      p2m: Addr -> list Rq;
      wait: bool;
      rob: Rob;
      ppc: Ppc
    }.

  Inductive Spec:
    (Proc -> SpecState) -> (Proc -> SpecState) -> Set :=
  | SpecFetch:
      forall f p st pc p2m w rob ppc,
        f p = (Build_SpecState st pc p2m w rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc p2m w (add rob (get ppc)) (nextPpc ppc)))
  | SpecExec:
      forall f p st pc p2m w rob ppc,
        f p = (Build_SpecState st pc p2m w rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc p2m w (compute rob) ppc))
  | SpecLoadRq:
      forall f p st pc p2m w rob ppc tag a,
        getLoad rob = Some (tag, a) ->
        f p = (Build_SpecState st pc p2m w rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc
                                         (updQ p2m a (LoadRq tag)) w (issueLoad rob tag) ppc))
  | SpecLoadRp:
      forall f p st pc p2m w rob ppc tag v p2m',
      forall a,
        p2m a = p2m' a ++ (LoadRq tag)::nil ->
        (forall a', a' <> a -> p2m a' = p2m' a') ->
        f p = (Build_SpecState st pc p2m w rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc p2m' w (updLoad rob tag v) ppc))
  | SpecAbort:
      forall f p st pc p2m rob ppc pc',
        getComPc rob = Some pc' -> pc' <> pc ->
        f p = (Build_SpecState st pc p2m false rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc p2m false (empty rob) (set ppc pc)))
  | SpecComNm:
      forall f p st pc p2m rob ppc nextPc delS,
        commit rob = Some (pc, Nmh nextPc delS) ->
        getDecodeElem pc st = (nextPc, Nm delS) ->
        f p = (Build_SpecState st pc p2m false rob ppc) ->
        Spec f (upd f p (Build_SpecState (updSt st delS) nextPc p2m false (retire rob) ppc))
  | SpecComStRq:
      forall f p st pc p2m rob ppc nextPc a v,
        commit rob = Some (pc, Storeh nextPc a v) ->
        getDecodeElem pc st = (nextPc, Store a v) ->
        f p = (Build_SpecState st pc p2m false rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc (updQ p2m a (StoreRq v)) true rob ppc))
  | SpecComStRp:
      forall f p st pc p2m rob ppc nextPc a v p2m',
        p2m a = p2m' a ++ StoreRq v::nil ->
        (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Storeh nextPc a v) ->
        getDecodeElem pc st = (nextPc, Store a v) ->
        f p = (Build_SpecState st pc p2m true rob ppc) ->
        Spec f (upd f p (Build_SpecState st nextPc p2m' false (retire rob) ppc))
  | SpecComLoadRq:
      forall f p st pc p2m rob ppc nextPc a v delS,
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        f p = (Build_SpecState st pc p2m false rob ppc) ->
        Spec f (upd f p (Build_SpecState st pc (updQ p2m a LoadCommitRq) true rob ppc))
  | SpecComLoadRpGood:
      forall f p st pc p2m rob ppc nextPc a v delS p2m',
        p2m a = p2m' a ++ LoadCommitRq::nil ->
        (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        getLoadDelta pc st v = delS ->
        f p = (Build_SpecState st pc p2m true rob ppc) ->
        Spec f (upd f p (Build_SpecState
                           (updSt st delS) nextPc p2m' false (retire rob) ppc))
  | SpecComLoadRpBad:
      forall f p st pc p2m rob ppc nextPc a v delS v' delS' p2m',
        p2m a = p2m' a ++ LoadCommitRq::nil ->
        (forall a', a' <> a -> p2m a' = p2m' a') ->
        commit rob = Some (pc, Loadh nextPc a v delS) ->
        getDecodeElem pc st = (nextPc, Load a) ->
        v <> v' ->
        getLoadDelta pc st v' = delS' ->
        f p = (Build_SpecState st pc p2m true rob ppc) ->
        Spec f (upd f p (Build_SpecState (updSt st delS') nextPc p2m' false
                                         (empty rob) (set ppc nextPc))).

  Definition getSpecIo s s' (t: Spec s s') :=
    match t with
      | SpecComLoadRpGood _ p _ _ _ _ _ _ a v _ _ _ _ _ _ _ _ =>
        Some (a, p, initData zero, Ld, v)
      | SpecComLoadRpBad _ p _ _ _ _ _ _ a _ _ v' _ _ _ _ _ _ _ _ _ =>
        Some (a, p, initData zero, Ld, v')
      | SpecComStRp _ p _ _ _ _ _ _ a v _ _ _ _ _ _ =>
        Some (a, p, v, St, initData zero)
      | SpecLoadRp _ p _ _ _ _ _ _ _ v _ a _ _ _ =>
        Some (a, p, initData zero, Ld, v)
      | _ => None
    end.

  Definition stateA1ToA2 s (p: Proc) :=
    Build_ProcState (pc (s p)) (st (s p)).

  Lemma noChange:
    forall f p v1 v2, f p = v1 ->
                      pc v2 = pc v1 ->
                      st v2 = st v1 ->
                      stateA1ToA2 (upd f p v2) = stateA1ToA2 f.
  Proof.
    intros.
    unfold stateA1ToA2.
    apply functional_extensionality.
    intros.
    unfold upd.
    destruct (decProc p x); simpl.
    rewrite H0, H1, <- H, e; reflexivity.
    reflexivity.
  Defined.

  Lemma sameThing:
    forall f p v2,
      upd (stateA1ToA2 f) p (Build_ProcState (pc v2) (st v2)) =
      (stateA1ToA2 (upd f p v2)).
  Proof.
    intros.
    unfold stateA1ToA2, upd in *.
    apply functional_extensionality.
    intros.
    destruct (decProc p x); reflexivity.
  Defined.

  Theorem convertSpecToCorrect s s' (t: Spec s s')
  : Correct (stateA1ToA2 s) (stateA1ToA2 s').
  Proof.
    destruct t;
    try (pose proof (Nothing (stateA1ToA2 f));
      match goal with
        | H: ?f ?p = ?v1 |- Correct (stateA1ToA2 ?f) (stateA1ToA2 (upd ?f ?p ?v2)) =>
          let H1 := fresh in
          let H2 := fresh in
          let H3 := fresh in
          assert (H1: pc v2 = pc v1) by reflexivity;
            assert (H2: st v2 = st v1) by reflexivity;
            pose proof (noChange _ _ _  H H1 H2) as H3;
            rewrite H3;
            intuition
    end).

    Ltac finishUse :=
    match goal with
      | H: ?f ?p = ?v1 |- Correct (stateA1ToA2 ?f) (stateA1ToA2 (upd ?f ?p ?v2)) =>
        let H2 := fresh in
        pose proof (@sameThing f p v2) as H2; simpl in *;
        rewrite H in *; simpl in *;
        rewrite <- H2; intuition
    end.

    assert (pc0 = getPc (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e1; reflexivity.
    assert (st0 = state (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e1; reflexivity.
    rewrite H, H0 in e0.
    pose proof (NonMem p (stateA1ToA2 f) e0).
    finishUse.

    assert (pc0 = getPc (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e3; reflexivity.
    assert (st0 = state (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e3; reflexivity.
    rewrite H, H0 in e2.
    pose proof (Str p (stateA1ToA2 f) e2).
    finishUse.

    assert (pc0 = getPc (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e4; reflexivity.
    assert (st0 = state (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e4; reflexivity.
    rewrite H, H0 in e2, e3.
    pose proof (Lod p (stateA1ToA2 f) e2 e3).
    finishUse.

    assert (pc0 = getPc (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e4; reflexivity.
    assert (st0 = state (stateA1ToA2 f p)).
    unfold stateA1ToA2; rewrite e4; reflexivity.
    rewrite H, H0 in e2, e3.
    pose proof (Lod p (stateA1ToA2 f) e2 e3).
    finishUse.

  Defined.

  Theorem bigCondition:
    forall a1 a1' (ta1: Spec a1 a1')
           b21 b21' (tb1: InstantMemory b21 b21')
           (a1b2EqIo: getSpecIo ta1 = getImIo tb1)
           (ta2: Correct (stateA1ToA2 a1) (stateA1ToA2 a1'))
           (a2Eq: ta2 = convertSpecToCorrect ta1)
           (a1a2EqIo: getSpecIo ta1 <> getCorrectIo (ta2)),
      {rec | getCorrectIo (convertSpecToCorrect ta1) = getImIo (tb2 rec) /\
             b21 = b2 rec /\ b21' = b2' rec}.
  Proof.
    intros.
    pose proof (exist (fun rec => getCorrectIo (convertSpecToCorrect ta1) = getImIo (tb2 rec) /\
   b21 = b2 rec /\ b21' = b2' rec) (Build_TransB2Rec _ b21 b21' tb1)).
    unfold getCorrectIo, getImIo; simpl.
    destruct ta1, tb1; (try discriminate); simpl in *; unfold eq_rec_r, eq_rec,
    eq_rect, eq_sym; simpl in *; try (
    match goal with
      | |- context [match ?P with _ => _ end] =>
        destruct P; simpl in *
    end;
      match goal with
        | H: ?Q -> {_|_} |- _ => let H1 := fresh in assert (H1:Q) by intuition;
                                                   apply (H H1)
      end).

    admit.

    Definition isNonMem a b (c : Correct a b) :=
      match c with
        | NonMem _ _ _ _ _ => True
        | _ => False
      end.

    Lemma cast_isNonMem : forall A (x y : A) a b (pf : x = y) e,
      isNonMem e
      -> isNonMem (match pf in _ = y' return Correct a (b y') with
                     | eq_refl => e
                   end).
    Proof.
      destruct pf; auto.
    Qed.

    Lemma match_isNonMem : forall a b (e : Correct a b) f1 f2,
      isNonMem e
      -> match e return option (Addr * Proc * Data * Desc * Data) with
           | Lod p _ a _ _ v _ _ => f1 a p v
           | Str p _ a _ v _ => f2 a p v
           | NonMem _ _ _ _ _ => None
           | Nothing _ => None
         end = None.
    Proof.
      destruct e; simpl; tauto.
    Qed.

    repeat unfold eq_rec_r, eq_rec, eq_rect,
    eq_sym, eq_ind, eq_ind_r, getCorrectIo in *.
    match goal with
      | H: ?ta2 = match ?P with _ => _ end |- _ => destruct P
    end.
    exfalso; subst.
    match goal with
      | H': _ <> ?P |- _ =>
            let final := fresh "final" in
            assert (final: P = None) by (apply match_isNonMem; apply cast_isNonMem;
                                         constructor);
              rewrite final in *; tauto
    end.

    Definition isStore a b (c : Correct a b) p0 a0 v0 :=
      match c with
        | Str p _ a _ v _ => p0 = p /\ a0 = a /\ v0 = v
        | _ => False
      end.

    Lemma cast_isStore : forall A (x y : A) a b (pf : x = y) e p0 a0 v0,
      isStore e p0 a0 v0
      -> isStore (match pf in _ = y' return Correct a (b y') with
                     | eq_refl => e
                   end) p0 a0 v0.
    Proof.
      destruct pf; auto.
    Qed.

    Lemma match_isStore : forall p0 a0 v0 a1 b1 (e : Correct a1 b1) f1 f2,
      isStore e p0 a0 v0
      -> match e return option (Addr * Proc * Data * Desc * Data) with
           | Lod p _ a _ _ v _ _ => f1 a p v
           | Str p _ a _ v _ => f2 a p v
           | NonMem _ _ _ _ _ => None
           | Nothing _ => None
         end = f2 a0 p0 v0.
    Proof.
      intros.
      unfold isStore in *.
      destruct e; intuition; subst; eauto.
    Qed.

    repeat unfold eq_rec_r, eq_rec, eq_rect,
    eq_sym, eq_ind, eq_ind_r, getCorrectIo in *.
    match goal with
      | H: ?ta2 = match ?P with _ => _ end |- _ => destruct P
    end.
    exfalso; subst.
    match goal with
      | H': _ <> ?P |- _ =>
            let final := fresh "final" in
            assert (final: P = Some (a, p, v, St, initData zero)) by
                (apply (@match_isStore p a v); apply cast_isStore; constructor; intuition);
              rewrite final in *; tauto
    end.

    Print Lod.
    Definition isLoad a b (c : Correct a b) p0 a0 v0 :=
      match c with
        | Lod p _ a _  _ v _ _ => p0 = p /\ a0 = a /\ v0 = v
        | _ => False
      end.

    Lemma cast_isLoad : forall A (x y : A) a b (pf : x = y) e p0 a0 v0,
      isLoad e p0 a0 v0
      -> isLoad (match pf in _ = y' return Correct a (b y') with
                     | eq_refl => e
                   end) p0 a0 v0.
    Proof.
      destruct pf; auto.
    Qed.

    Lemma match_isLoad : forall p0 a0 v0 a1 b1 (e : Correct a1 b1) f1 f2,
      isLoad e p0 a0 v0
      -> match e return option (Addr * Proc * Data * Desc * Data) with
           | Lod p _ a _ _ v _ _ => f1 a p v
           | Str p _ a _ v _ => f2 a p v
           | NonMem _ _ _ _ _ => None
           | Nothing _ => None
         end = f1 a0 p0 v0.
    Proof.
      intros.
      unfold isLoad in *.
      destruct e; intuition; subst; eauto.
    Qed.

    repeat unfold eq_rec_r, eq_rec, eq_rect,
    eq_sym, eq_ind, eq_ind_r, getCorrectIo in *.
    match goal with
      | H: ?ta2 = match ?P with _ => _ end |- _ => destruct P
    end.
    exfalso; subst.
    match goal with
      | H': _ <> ?P |- _ =>
            let final := fresh "final" in
            assert (final: P = Some (a, p, initData zero, Ld, v)) by
                (apply (@match_isLoad p a v); apply cast_isLoad; constructor; intuition);
              rewrite final in *; tauto
    end.

    repeat unfold eq_rec_r, eq_rec, eq_rect,
    eq_sym, eq_ind, eq_ind_r, getCorrectIo in *.
    match goal with
      | H: ?ta2 = match ?P with _ => _ end |- _ => destruct P
    end.
    exfalso; subst.
    match goal with
      | H': _ <> ?P |- _ =>
            let final := fresh "final" in
            assert (final: P = Some (a, p, initData zero, Ld, v')) by
                (apply (@match_isLoad p a v'); apply cast_isLoad; constructor; intuition);
              rewrite final in *; tauto
    end.
  Qed.
