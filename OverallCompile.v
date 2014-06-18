Require Import Omega.
Set Implicit Arguments.

(* Defining transitions and streams associated with transitions 
 * A transition has two properties: IO and Arch
 * IO defines the interaction of the transtion with other transitions
 * Arch defines the properties of this transition that we care about
 *)
Section GeneralTransitions.
  Variable State: Set.
  Definition AllTransitions := State -> State -> Set.

  Section OneTransition.
    Variable Transition: AllTransitions.
    CoInductive Stream: State -> Set :=
      | TCons s s': Transition s s' -> Stream s' -> Stream s.

    Variable Io: Set.
    
    Definition GetTransitionIo := forall s s' (t: Transition s s'), Io.

    Variable getTransitionIo: GetTransitionIo.

    Fixpoint getStreamState n s (ts: Stream s): State * State :=
      match ts with
        | TCons s s' _ ts' => match n with
                                | 0 => (s, s')
                                | S m => getStreamState m ts'
                              end
      end.

    Theorem stateNSndStateSnFst n: forall s (ts: Stream s),
                                     snd (getStreamState n ts) = fst (getStreamState (S n) ts).
    Proof.
      induction n.
      intros.
      simpl.

      destruct ts.
      destruct ts.
      reflexivity.

      intros.
      destruct ts.
      simpl.
      specialize (IHn _ ts).
      assumption.
    Qed.

    Fixpoint getStreamTransition n s (ts: Stream s): Transition (fst (getStreamState n ts))
                                                                (snd (getStreamState n ts)) :=
      match ts with
        | TCons _ _ t ts' => match n with
                                | 0 => t
                                | S m => getStreamTransition m ts'
                              end
      end.


    Definition getStreamIo n s (ts: Stream s): Io :=
      getTransitionIo (getStreamTransition n ts).
  End OneTransition.
End GeneralTransitions.

Section SimulateTransitions.
  Variable StateA StateB: Set.
  Variable TransA: AllTransitions StateA.
  Variable TransB: AllTransitions StateB.
  Variable getBFromA: StateA -> StateB.
  Variable getTransBFromA: forall sa sa' (ta: TransA sa sa'), TransB (getBFromA sa)
                                                                     (getBFromA sa').

  CoFixpoint createStreamB sa (ta: Stream TransA sa): Stream TransB (getBFromA sa) :=
    match ta in Stream _ sa' return sa = sa' -> Stream TransB (getBFromA sa') with
      | TCons s s' t ta' => fun _ => TCons (getBFromA s) (getTransBFromA t) (createStreamB ta')
    end eq_refl.

  Theorem streamTransSimulate n:
    forall sa (sas: Stream TransA sa),
      getBFromA (fst (getStreamState n sas)) = fst (getStreamState n (createStreamB sas)).
  Proof.
    induction n.
    intros.
    destruct sas.
    reflexivity.
    intros.
    destruct sas.
    specialize (IHn _ sas).
    assumption.
  Qed.

  Theorem streamTransSimulateEx:
    forall sa (sas: Stream TransA sa),
      exists (sbs: Stream TransB (getBFromA sa)),
        forall n,
          getBFromA(fst (getStreamState n sas)) = fst (getStreamState n sbs).
  Proof.
    intros.
    exists (createStreamB sas).
    intros.
    apply (streamTransSimulate n sas).
  Qed.
End SimulateTransitions.

(* Definition of a transition or a stream of transitions being simulated by other
 * transition or stream of transitions
 * StreamIoSimulate: Says that B simulates A iff for every stream-A,
 * there exists stream-B, such that nth IO of A is the nth IO of B
 *)

Section SimulateIoDefns.
  Variable StateA StateB Io: Set.
  Variable TransA: AllTransitions StateA.
  Variable TransB: AllTransitions StateB.
  Variable getTransAIo: GetTransitionIo TransA Io.
  Variable getTransBIo: GetTransitionIo TransB Io.

  Definition StreamIoSimulate :=
    forall sa (sas: Stream TransA sa),
    exists sb (sbs: Stream TransB sb),
      forall n,
        getStreamIo getTransAIo n sas = getStreamIo getTransBIo n sbs.
End SimulateIoDefns.

(* Parallely composing two transitions with matching IOs
 * We ensure that each transition is executed simultaneously, and the IOs match
 * A + B
 *)
Section ParallelCompose.
  Variable StateA StateB Io: Set.
  Variable TransA: AllTransitions StateA.
  Variable TransB: AllTransitions StateB.
  Variable getTransAIo: GetTransitionIo TransA Io.
  Variable getTransBIo: GetTransitionIo TransB Io.

  Inductive TransAB: AllTransitions (StateA*StateB) :=
    | ABTrans sa1 sa2 (ta: TransA sa1 sa2) sb1 sb2 (tb: TransB sb1 sb2):
        getTransAIo ta = getTransBIo tb -> TransAB (sa1, sb1) (sa2, sb2).

  Definition getStreamATrans x (sab: Stream TransAB x) n:
    TransA (fst (fst (getStreamState n sab))) (fst (snd (getStreamState n sab))) :=
    match getStreamTransition n sab in TransAB x y return TransA (fst x) (fst y) with
      | ABTrans _ _ ta _ _ _ _ => ta
    end.

  Definition getStreamBTrans x (sab: Stream TransAB x) n:
    TransB (snd (fst (getStreamState n sab))) (snd (snd (getStreamState n sab))) :=
    match getStreamTransition n sab in TransAB x y return TransB (snd x) (snd y) with
      | ABTrans _ _ _ _ _ ta _ => ta
    end.

  Definition getStreamEq x (sab: Stream TransAB x) n :=
    match getStreamTransition n sab as t0 return match t0 with
                                                   | ABTrans _ _ ta _ _ tb _ =>
                                                     getTransAIo ta = getTransBIo tb
                                                 end with
      | ABTrans _ _ _ _ _ _ me => me
    end.

  CoFixpoint getStreamA x (sab: Stream TransAB x): Stream TransA (fst x) :=
    match sab with
      | TCons _ _ t sab' =>
        match t in TransAB s1 s2 return Stream TransAB s2 -> Stream TransA (fst s1) with
          | ABTrans _ _ ta _ _ tb _ =>
            fun sab' => TCons _ ta (getStreamA sab')
        end sab'
    end.

  CoFixpoint getStreamB x (sab: Stream TransAB x): Stream TransB (snd x) :=
    match sab with
      | TCons _ _ t sab' =>
        match t in TransAB s1 s2 return Stream TransAB s2 -> Stream TransB (snd s1) with
          | ABTrans _ _ ta _ _ tb _ =>
            fun sab' => TCons _ tb (getStreamB sab')
        end sab'
    end.

  Lemma streamTa n: forall x (sab: Stream TransAB x),
    getStreamIo getTransAIo n (getStreamA sab) = getTransAIo (getStreamATrans sab n).
  Proof.
    induction n.
    intros.
    destruct sab.
    unfold getStreamIo, getStreamATrans.
    simpl.
    destruct t.
    reflexivity.
    intros.
    destruct sab.
    unfold getStreamIo, getStreamATrans.
    simpl.
    destruct t.
    specialize (IHn _ sab).
    assumption.
  Qed.

  Lemma streamTb n: forall x (sab: Stream TransAB x),
    getStreamIo getTransBIo n (getStreamB sab) = getTransBIo (getStreamBTrans sab n).
  Proof.
    induction n.
    intros.
    destruct sab.
    unfold getStreamIo, getStreamBTrans.
    simpl.
    destruct t.
    reflexivity.
    intros.
    destruct sab.
    unfold getStreamIo, getStreamBTrans.
    simpl.
    destruct t.
    specialize (IHn _ sab).
    assumption.
  Qed.

  Theorem streamStateEq n: forall x (sab: Stream TransAB x),
    getStreamState n sab = ((fst (getStreamState n (getStreamA sab)), 
                             fst (getStreamState n (getStreamB sab))),
                            (snd (getStreamState n (getStreamA sab)),
                             snd (getStreamState n (getStreamB sab)))).
  Proof.
    induction n.
    intros.
    destruct sab.
    simpl.
    destruct t.
    reflexivity.
    intros.
    destruct sab.
    simpl.
    destruct t.
    apply (IHn _ sab).
  Qed.


  Theorem streamIoEq x (sab: Stream TransAB x) n:
    getStreamIo getTransAIo n (getStreamA sab) = getStreamIo getTransBIo n (getStreamB sab).
  Proof.
    pose proof (streamTa n sab).
    pose proof (streamTb n sab).
    rewrite H, H0. clear H H0.
    unfold getStreamATrans, getStreamBTrans.
    destruct (getStreamTransition n sab).
    intuition.
  Qed.

  Section BuildTransAB.
    Variable a: StateA.
    Variable b: StateB.
    Variable sa: Stream TransA a.
    Variable sb: Stream TransB b.
    Variable ioMatch: forall n, getStreamIo getTransAIo n sa = getStreamIo getTransBIo n sb.

    Lemma nextIoMatch n:
      (snd (getStreamState n sa), snd (getStreamState n sb)) =
      (fst (getStreamState (S n) sa), fst (getStreamState (S n) sb)).
    Proof.
      pose proof (stateNSndStateSnFst n sa).
      pose proof (stateNSndStateSnFst n sb).
      rewrite H, H0.
      reflexivity.
    Qed.

    CoFixpoint buildTransAB n:
      Stream TransAB (fst (getStreamState n sa), fst (getStreamState n sb)) :=
      TCons _ (ABTrans (ioMatch n)) (eq_rect_r _ (buildTransAB (S n)) (nextIoMatch n)).

    Lemma abStateEq n: forall r (ls: Stream TransAB r) r' (pf: r' = r),
                         getStreamState n (eq_rect_r _ ls pf) = getStreamState n ls.
    Proof.
      intros.
      rewrite pf.
      destruct ls.
      reflexivity.
    Qed.

    Lemma buildTransDistr n:
      forall m,
        fst (getStreamState n (buildTransAB m)) =
        (fst (getStreamState (n+m) sa), fst (getStreamState (n+m) sb)).
    Proof.
      induction n.
      intros m.
      assert (0+m = m) by omega.
      rewrite H.
      reflexivity.
      intros m.
      assert (S n + m = n + S m) by omega.
      specialize (IHn (S m)).
      rewrite H.
      rewrite <- IHn.
      simpl.
      f_equal.
      apply (abStateEq n (buildTransAB (S m)) (nextIoMatch m)).
    Qed.

    Lemma getStateFinally n:
      fst (getStreamState n (buildTransAB 0)) = (fst (getStreamState n sa),
                                                 fst (getStreamState n sb)).
    Proof.
      pose proof (buildTransDistr n 0).
      assert (n+0 = n) by omega.
      rewrite H0 in *.
      assumption.
    Qed.

    Lemma getStateABGetStateA n:
      fst (fst (getStreamState n (buildTransAB 0))) = fst (getStreamState n sa).
    Proof.
      pose proof (getStateFinally n).
      destruct (fst (getStreamState n (buildTransAB 0))).
      injection H; intros.
      intuition.
    Qed.

  End BuildTransAB.
End ParallelCompose.

(* Given A1 transition can be converted to A2
 * Given B1 is stream-io-simulated by B2
 * Then, (A1+B1) can be stream-trans-simulated by (A2+B2)
 * Proof:
 * B2 stream-io-simulates B1, so the IOs match
 * So, the IOs match with A1
 * So, (A1+B2) stream-io-simulates (A1+B1) and the state of A1, A1 match in every transition
 * If (A1+B2) transition can be converted to (A2+B2), then the getBFromA state of (A1+B2)
 * matches with state of (A2+B2) in every transition.
 * In particular, the getBFromA state of A1 matches with state of A2 in every transition
 * So the state of A1 in (A1+B1) is matched with state of A2 in (A2+B2) in every transition
 *
 * If we didn't have (A1+B2) transition can be converted to (A2+B2).
 * Instead we have A1 transition can be converted to A2 transition, and during
 * this conversion, either A1's IO matches with A2,
 * or the effect of A1's IO on B2 is the same as the effect of A2's IO on B2
 * for that transition, ie B2's state changes in the same way.
 * 
 * In terms of correlation with actual system,
 * Think of A1 = N speculating processors
 * Think of A2 = N simple processors
 * Think of B1 = Caches
 * Think of B2 = Atomic Memory
 * Think of some proof where if I prove for 1-speculating-processor
 * can be transition-arch-simulated by 1-simple-processor, then I can prove it for N
 * (ie A1 by A2)
 * B1 stream-io-simulated by B2 is proved
 *)
Section ComplexSimulate.
  Variable StateA1 StateA2 StateB1 StateB2 Io: Set.
  Variable TransA1: AllTransitions StateA1.
  Variable TransA2: AllTransitions StateA2.
  Variable TransB1: AllTransitions StateB1.
  Variable TransB2: AllTransitions StateB2.
  Variable getTransA1Io: GetTransitionIo TransA1 Io.
  Variable getTransA2Io: GetTransitionIo TransA2 Io.
  Variable getTransB1Io: GetTransitionIo TransB1 Io.
  Variable getTransB2Io: GetTransitionIo TransB2 Io.
  Variable getA2FromA1: StateA1 -> StateA2.
  Variable getB2FromB1: StateB1 -> StateB2.

  Definition TransA1B1 := TransAB getTransA1Io getTransB1Io.
  Definition TransA1B2 := TransAB getTransA1Io getTransB2Io.
  Definition TransA2B2 := TransAB getTransA2Io getTransB2Io.

  Record TransB2Rec :=
    { b2: StateB2;
      b2': StateB2;
      tb2: TransB2 b2 b2'
    }. 

  (* (A1+B2) transition can be converted to (A2+B2), B2 stream-io-simulates B1 ->
   * (A1+B1) transition can be converted to (A2+B2) where states match *)
  Section StatesMatch.
    Variable convertA1B2ToA2B2:
      (forall a1b2 a1b2', TransA1B2 (a1b2) (a1b2') ->
                             TransA2B2 ((fun x => (getA2FromA1 (fst x), (snd x))) a1b2)
                                       ((fun x => (getA2FromA1 (fst x), (snd x))) a1b2')).
    Variable convertB1ToB2:
      (forall b1 (sb1: Stream TransB1 b1),
       exists b2 (sb2: Stream TransB2 b2),
         forall n, getStreamIo getTransB1Io n sb1 = getStreamIo getTransB2Io n sb2).

    Theorem statesMatch:
      forall a1 b1 (sa1b1: Stream TransA1B1 (a1,b1)),
        exists a2 b2 (sa2b2: Stream TransA2B2 (a2,b2)),
          forall n, getA2FromA1 (fst (fst (getStreamState n sa1b1))) =
                    fst (fst (getStreamState n sa2b2)).
    Proof.
      intros.
      pose (getStreamA sa1b1) as sa1.
      pose (getStreamB sa1b1) as sb1.
      simpl in *.
      destruct (convertB1ToB2 sb1) as [b2 [sb2 ioMatch]].
      pose proof (streamIoEq sa1b1) as Y.
      fold sa1 in Y.
      fold sb1 in Y.
      assert (H: forall n,
                   getStreamIo getTransA1Io n sa1 = getStreamIo getTransB2Io n sb2).
      intros.
      specialize (ioMatch n).
      specialize (Y n).
      rewrite <- ioMatch.
      assumption.

      pose (buildTransAB _ _ _ _ H 0) as B.

      pose proof (streamTransSimulateEx _ (fun x => (getA2FromA1 (fst x), (snd x)))
                                        convertA1B2ToA2B2 B) as [sbs reset].
      exists (fst ((fun x => (getA2FromA1 (fst x), (snd x)))
                     (fst (getStreamState 0 sa1), fst (getStreamState 0 sb2)))).
      exists (snd ((fun x => (getA2FromA1 (fst x), (snd x)))
                     (fst (getStreamState 0 sa1), fst (getStreamState 0 sb2)))).
      exists sbs.
      intros n.
      specialize (reset n).
      pose proof (getStateABGetStateA getTransA1Io getTransB2Io sa1 sb2 H n) as u1.
      fold B in u1.
      assert (u2: fst (getStreamState n sbs) = (fst (fst (getStreamState n sbs)),
                                                snd (fst (getStreamState n sbs)))).
      destruct (fst (getStreamState n sbs)).
      reflexivity.
      rewrite u2 in reset.
      injection reset; intros u3 u4.
      clear u2 reset.
      pose proof (streamStateEq n sa1b1) as stmEq.
      fold sa1 in stmEq.
      fold sb1 in stmEq.
      assert (u5: fst (fst (getStreamState n sa1b1)) =
                  fst (fst (fst (getStreamState n sa1), fst (getStreamState n sb1),
          (snd (getStreamState n sa1), snd (getStreamState n sb1))))).
      f_equal; f_equal; assumption.
      simpl in u5.
      rewrite u5.
      assert (u6: getA2FromA1 (fst (fst (getStreamState n B))) =
                  getA2FromA1 (fst (getStreamState n sa1))).
      f_equal; assumption.
      rewrite <- u6.
      assumption.
    Qed.      
  End StatesMatch.

  (*
   * To Prove: (A1+B2) transition can be converted to (A2+B2)
   * Given: A1 can be converted to A2 and
   *        For each converted transition, the state change that happens in B2 matches
   *)
  Section ProvingStatesMatch1.
    Variable convertA1ToA2:
      (forall a1 a1', TransA1 a1 a1' ->
                      TransA2 (getA2FromA1 a1) (getA2FromA1 a1')).

    Variable bigCondition:
      forall a1 a1' (ta1: TransA1 a1 a1')
             b21 b21' (tb1: TransB2 b21 b21')
             (a1b2EqIo: getTransA1Io ta1 = getTransB2Io tb1),
        {rec | getTransA2Io (convertA1ToA2 ta1) = getTransB2Io (tb2 rec) /\ b21 = b2 rec /\ b21' = b2' rec}.

    Theorem canConvert:
      forall x x', TransA1B2 x x' ->
                   TransA2B2 (getA2FromA1 (fst x), snd x) (getA2FromA1 (fst x'), snd x').
    Proof.
      intros.
      destruct H.
      simpl.
      pose proof (bigCondition e) as [tbnew [pf [u2 u3]]].
      subst.
      apply (ABTrans getTransA2Io getTransB2Io _ _ _ _ _ _ pf).
    Qed.

    Variable convertB1ToB2:
      (forall b1 (sb1: Stream TransB1 b1),
       exists b2 (sb2: Stream TransB2 b2),
         forall n, getStreamIo getTransB1Io n sb1 = getStreamIo getTransB2Io n sb2).

    Theorem statesMatchBigCond:
      forall a1 b1 (sa1b1: Stream TransA1B1 (a1,b1)),
        exists a2 b2 (sa2b2: Stream TransA2B2 (a2,b2)),
          forall n, getA2FromA1 (fst (fst (getStreamState n sa1b1))) =
                    fst (fst (getStreamState n sa2b2)).
    Proof.
      intros.
      apply (statesMatch canConvert convertB1ToB2 sa1b1).
    Qed.
    
  End ProvingStatesMatch1.

  (*
   * For each converted transition from A1 to A2 (in the presence of B2),
   * if either IO matches between A1 and A2 or
   *           there exists a transition in B2 corresponding to IO of A2's transition
   * then for each converted transition, the state change that happens in B2 matches
   *)
  Section ProvingStatesMatch2.
    Variable convertA1ToA2:
      (forall a1 a1', TransA1 a1 a1' ->
                      TransA2 (getA2FromA1 a1) (getA2FromA1 a1')).

    Variable bigCond2:
      forall a1 a1' (ta1: TransA1 a1 a1')
             bi2 bi2' (tb: TransB2 bi2 bi2'),
        getTransA1Io ta1 = getTransB2Io tb ->
        getTransA1Io ta1 <> getTransA2Io (convertA1ToA2 ta1) ->
        {rec: TransB2Rec | getTransA2Io (convertA1ToA2 ta1) = getTransB2Io (tb2 rec)
                           /\ bi2 = (b2 rec) /\ bi2' = (b2' rec)}.

    Variable decIo: forall a1 a2: Io, {a1=a2}+{a1<>a2}.

    Theorem bigCondition:
      forall a1 a1' (ta1: TransA1 a1 a1')
             b21 b21' (tb1: TransB2 b21 b21')
             (a1b2EqIo: getTransA1Io ta1 = getTransB2Io tb1),
        {rec | getTransA2Io (convertA1ToA2 ta1) = getTransB2Io (tb2 rec) /\ b21 = b2 rec /\ b21' = b2' rec}.
    Proof.
      intros.
      specialize (bigCond2 a1b2EqIo).
      destruct (decIo (getTransA1Io ta1) (getTransA2Io (convertA1ToA2 ta1))).
      assert (getTransA2Io (convertA1ToA2 ta1) = getTransB2Io tb1).
      rewrite e in *; intuition.
      assert (help: getTransA2Io (convertA1ToA2 ta1) = getTransB2Io tb1 /\ b21 = b21 /\ b21' = b21') by
             intuition.
      pose (Build_TransB2Rec tb1) as sth.
      apply (exist _ sth); intuition.
      apply (@bigCond2 n).
    Qed.

    Variable convertB1ToB2:
      (forall b1 (sb1: Stream TransB1 b1),
       exists b2 (sb2: Stream TransB2 b2),
         forall n, getStreamIo getTransB1Io n sb1 = getStreamIo getTransB2Io n sb2).

    Theorem statesMatchBigCond2:
      forall a1 b1 (sa1b1: Stream TransA1B1 (a1,b1)),
        exists a2 b2 (sa2b2: Stream TransA2B2 (a2,b2)),
          forall n, getA2FromA1 (fst (fst (getStreamState n sa1b1))) =
                    fst (fst (getStreamState n sa2b2)).
    Proof.
      apply (statesMatchBigCond convertA1ToA2 bigCondition convertB1ToB2).
    Qed.
  End ProvingStatesMatch2.

End ComplexSimulate.
