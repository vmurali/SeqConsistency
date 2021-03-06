(* Copyright (c) 2015 Muralidaran Vijayaraghavan vmurali@csail.mit.edu *)


(* Permission is hereby granted, free of charge, to any person obtaining *)
(* a copy of this software and associated documentation files (the *)
(* "Software"), to deal in the Software without restriction, including *)
(* without limitation the rights to use, copy, modify, merge, publish, *)
(* distribute, sublicense, and/or sell copies of the Software, and to *)
(* permit persons to whom the Software is furnished to do so, subject to *)
(* the following conditions: *)

(* The above copyright notice and this permission notice shall be *)
(* included in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE *)
(* LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION *)
(* OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION *)
(* WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. *)


Require Import SeqConsistency.Useful SeqConsistency.DataTypes List Coq.Logic.FunctionalExtensionality SeqConsistency.TransitionsNew SeqConsistency.StoreAtomicity.

Set Implicit Arguments.

Section AddrDataProc.
  Variable Addr Data Proc: Set.
  Variable zero: Addr.
  Variable decAddr: forall a1 a2: Addr, {a1=a2}+{a1<>a2}.
  Variable decProc: forall p1 p2: Proc, {p1=p2}+{p1<>p2}.
  Variable initData: Addr -> Data.



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

  Variable pc0 : Pc.
  Variable state0 : PState.
  Definition initProcState := Build_ProcState pc0 state0.

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

    Variable rob0 : Rob.
    Variable ppc0 : Ppc.
    Definition initSpecState := Build_SpecState state0 pc0 (fun a => nil) false rob0 ppc0.

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

    Variable StateB1: Set.
    Variable b1: StateB1.
    Variable TransB1: AllTransitions StateB1.
    Variable getTransB1Io: GetTransitionIo TransB1 (option (Addr * Proc * Data * Desc *
                                                            Data)).
    Variable sa1b1: Stream (TransAB getSpecIo getTransB1Io) (fun p => initSpecState, b1).
    Variable sb2: Stream (InstantMemory Proc decAddr) initData.
    Variable sb2Simulate:
      forall n,
        getStreamIo getTransB1Io n (getStreamB sa1b1) =
        getStreamIo (getImIo zero initData) n sb2.

    Theorem convertSpecToCorrect' s s' (t: Spec s s')
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

      assert (pc1 = getPc (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e1; reflexivity.
      assert (st0 = state (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e1; reflexivity.
      rewrite H, H0 in e0.
      pose proof (NonMem p (stateA1ToA2 f) e0).
      finishUse.

      assert (pc1 = getPc (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e3; reflexivity.
      assert (st0 = state (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e3; reflexivity.
      rewrite H, H0 in e2.
      pose proof (Str p (stateA1ToA2 f) e2).
      finishUse.

      assert (pc1 = getPc (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e4; reflexivity.
      assert (st0 = state (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e4; reflexivity.
      rewrite H, H0 in e2, e3.
      pose proof (Lod p (stateA1ToA2 f) e2 e3).
      finishUse.

      assert (pc1 = getPc (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e4; reflexivity.
      assert (st0 = state (stateA1ToA2 f p)).
      unfold stateA1ToA2; rewrite e4; reflexivity.
      rewrite H, H0 in e2, e3.
      pose proof (Lod p (stateA1ToA2 f) e2 e3).
      finishUse.

    Defined.


    Theorem convertSpecToCorrect:
      forall n, Correct (stateA1ToA2 (fst (fst (getStreamState n sa1b1))))
                        (stateA1ToA2 (fst (snd (getStreamState n sa1b1)))).
    Proof.
      intros n.
      apply (convertSpecToCorrect' (getStreamATrans sa1b1 n)).
    Defined.

    Definition InstantMemory := @InstantMemory Addr Data Proc decAddr.
    Definition getImIo := @getImIo Addr Data Proc zero decAddr initData.
    Definition IReq := @IReq Addr Data Proc decAddr.
    Definition IIdle := @IIdle Addr Data Proc decAddr.

    Theorem bigCondition:
      forall n,
        getSpecIo (getStreamATrans sa1b1 n) <> getCorrectIo (convertSpecToCorrect n) ->
        {x: InstantMemory (fst (getStreamState n sb2)) (snd (getStreamState n sb2))|
         getCorrectIo (convertSpecToCorrect n) = getImIo x}.
    Proof.
      intros.
      specialize (sb2Simulate n).
      pose proof (streamTa n sa1b1) as u1.
      pose proof (streamTb n sa1b1) as u2.
      pose proof (streamIoEq sa1b1 n) as u3.
      rewrite u2 in *.
      rewrite <- u3 in *.
      rewrite u1 in *.

      (*pose proof (exist (fun x => getCorrectIo (convertSpecToCorrect n) =
                         getImIo x) (getStreamTransition sb2 n)) as u4. *)

      unfold convertSpecToCorrect, convertSpecToCorrect' in *; simpl in *.

      Definition isNonMem a b (c : Correct a b) :=
        match c with
          | NonMem _ _ _ _ _ => True
          | Nothing _ => True
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
                               -> None = match e return option (Addr * Proc * Data * Desc * Data) with
                                    | Lod p _ a _ _ v _ _ => f1 a p v
                                    | Str p _ a _ v _ => f2 a p v
                                    | NonMem _ _ _ _ _ => None
                                    | Nothing _ => None
                                  end.
      Proof.
        destruct e; simpl; tauto.
      Qed.

      destruct (getStreamATrans sa1b1 n); unfold eq_rec_r, eq_rec, eq_rect, eq_sym,
                                          getCorrectIo, getImIo, getStreamIo,
                                          StoreAtomicity.getImIo in *;
      simpl in *; destruct (getStreamTransition sb2 n); try discriminate;
      try match goal with
            | H: _ <> ?P |- _ => assert (None = P) by (apply match_isNonMem;
                                                       repeat (apply cast_isNonMem);
                                                       constructor); intuition
          end.

      Axiom cheat: forall t, t.
      match goal with
        | |- {_|match ?P with _ => _ end = _} =>
          destruct P; try discriminate
      end.
      injection sb2Simulate; intros.
      rewrite <- H2.

      apply (exist
                    (fun x => None = match x with
                                       | StoreAtomicity.IReq a1 p2 d0 w1 =>
                                         Some
                                           (a1, p2, d0, w1,
                                            if w1
                                            then fst (getStreamState n sb2) a1
                                            else initData zero)
                                       | StoreAtomicity.IIdle => None
                                     end)
                    (StoreAtomicity.IIdle Proc decAddr (fst (getStreamState n sb2)))).
      intuition.

      injection sb2Simulate; intros.
      rewrite <- H2.
      
      apply (exist
                    (fun x => None = match x with
                                       | StoreAtomicity.IReq a1 p2 d0 w1 =>
                                         Some
                                           (a1, p2, d0, w1,
                                            if w1
                                            then fst (getStreamState n sb2) a1
                                            else initData zero)
                                       | StoreAtomicity.IIdle => None
                                     end)
                    (StoreAtomicity.IIdle Proc decAddr (fst (getStreamState n sb2)))).
      intuition.


      Definition isStore p0 a0 v0 a b (c : Correct a b) :=
        match c with
          | Str p _ a _ v _ => p0 = p /\ a0 = a /\ v0 = v
          | _ => False
        end.

      Lemma cast_isStore : forall p0 a0 v0 A (x y : A) a b (pf : x = y) e,
                             isStore p0 a0 v0 e
                             -> isStore p0 a0 v0
                                        (match pf in _ = y' return Correct a (b y') with
                                           | eq_refl => e
                                         end).
      Proof.
        destruct pf; auto.
      Qed.

      Lemma match_isStore : forall p0 a0 v0 a1 b1 (e : Correct a1 b1),
                              isStore p0 a0 v0 e
                              -> Some (a0,p0,v0,St,initData zero) =
                                 match e return
                                       option (Addr * Proc * Data * Desc * Data) with
                                   | Lod p _ a _ _ v _ _ => Some (a, p, initData zero, Ld, v)
                                   | Str p _ a _ v _ => Some (a, p, v, St, initData zero)
                                   | NonMem _ _ _ _ _ => None
                                   | Nothing _ => None
                                 end.
      Proof.
        intros.
        unfold isStore in *.
        destruct e; intuition; subst; eauto.
      Qed.

      match goal with
        | H: _ <> ?P |- _ => assert (Some (a, p, v, St, initData zero) = P)
      end.

      apply (match_isStore p a v).
      repeat (apply (cast_isStore p a v)).
      constructor; intuition.
      intuition.

      About Lod.
      Definition isLoad p0 a0 v0 a b (c : Correct a b) :=
        match c with
          | Lod p _ a _ _ v _ _ => p0 = p /\ a0 = a /\ v0 = v
          | _ => False
        end.

      Lemma cast_isLoad : forall p0 a0 v0 A (x y : A) a b (pf : x = y) e,
                             isLoad p0 a0 v0 e
                             -> isLoad p0 a0 v0
                                        (match pf in _ = y' return Correct a (b y') with
                                           | eq_refl => e
                                         end).
      Proof.
        destruct pf; auto.
      Qed.

      Lemma match_isLoad : forall p0 a0 v0 a1 b1 (e : Correct a1 b1),
                              isLoad p0 a0 v0 e
                              -> Some (a0,p0,initData zero,Ld,v0) = match e return option (Addr * Proc * Data * Desc * Data) with
                                   | Lod p _ a _ _ v _ _ => Some (a, p, initData zero, Ld, v)
                                   | Str p _ a _ v _ => Some (a, p, v, St, initData zero)
                                   | NonMem _ _ _ _ _ => None
                                   | Nothing _ => None
                                 end.
      Proof.
        intros.
        unfold isLoad in *.
        destruct e; intuition; subst; eauto.
      Qed.

      match goal with
        | H: _ <> ?P |- _ => assert (Some (a, p, initData zero, Ld, v) = P)
      end.

      apply (match_isLoad p a v).
      repeat (apply (cast_isLoad p a v)).
      constructor; intuition.
      intuition.

      match goal with
        | H: _ <> ?P |- _ => assert (Some (a, p, initData zero, Ld, v') = P)
      end.

      apply (match_isLoad p a v').
      repeat (apply (cast_isLoad p a v')).
      constructor; intuition.
      intuition.
    Qed.

    Variable decData: forall d1 d2: Data, {d1=d2}+{d1<>d2}.
    Theorem decIo: forall i1 i2: option (Addr * Proc * Data * Desc * Data), {i1=i2}+{i1 <> i2}.
    Proof.
      intros.
      decide equality.
      destruct a,p.
      decide equality.
      destruct a,p1.
      decide equality.
      decide equality.
      destruct a,p3.
      decide equality.
      decide equality.
    Qed.
    About statesMatch.

    Definition stMatch :=
      statesMatch getCorrectIo getImIo stateA1ToA2 decIo
                  sa1b1 sb2 sb2Simulate convertSpecToCorrect bigCondition.
  End PerProc.
End AddrDataProc.

About stMatch.