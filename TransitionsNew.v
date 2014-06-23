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

    Fixpoint getStreamTransition s (ts: Stream s) n: Transition (fst (getStreamState n ts))
                                                                (snd (getStreamState n ts)) :=
      match ts with
        | TCons _ _ t ts' => match n with
                                | 0 => t
                                | S m => getStreamTransition ts' m
                              end
      end.

    Theorem nextStmEq s s' (t: Transition s s') (ts: Stream s') n :
      getStreamTransition ts n = getStreamTransition (TCons t ts) (S n).
    Proof.
      reflexivity.
    Qed.

    Definition getStreamIo n s (ts: Stream s): Io :=
      getTransitionIo (getStreamTransition ts n).
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

Section SimulateIo.
  Variable StateA StateB StateC Io: Set.
  Variable TransA: AllTransitions StateA.
  Variable TransB: AllTransitions StateB.
  Variable TransC: AllTransitions StateC.
  Variable getTransAIo: GetTransitionIo TransA Io.
  Variable getTransBIo: GetTransitionIo TransB Io.
  Variable getTransCIo: GetTransitionIo TransC Io.

  Theorem ioSimulateTransitive:
    StreamIoSimulate getTransAIo getTransBIo ->
    StreamIoSimulate getTransBIo getTransCIo ->
    StreamIoSimulate getTransAIo getTransBIo.
  Proof.
    intuition.
  Qed.
End SimulateIo.

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
    match getStreamTransition sab n in TransAB x y return TransA (fst x) (fst y) with
      | ABTrans _ _ ta _ _ _ _ => ta
    end.

  Definition getStreamBTrans x (sab: Stream TransAB x) n:
    TransB (snd (fst (getStreamState n sab))) (snd (snd (getStreamState n sab))) :=
    match getStreamTransition sab n in TransAB x y return TransB (snd x) (snd y) with
      | ABTrans _ _ _ _ _ ta _ => ta
    end.

  Definition getStreamEq x (sab: Stream TransAB x) n :=
    match getStreamTransition sab n as t0 return match t0 with
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
    destruct (getStreamTransition sab n).
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

  Variable decIo: forall i1 i2: Io, {i1=i2}+{i1<>i2}.

  Definition TransA1B1 := TransAB getTransA1Io getTransB1Io.
  Definition TransA1B2 := TransAB getTransA1Io getTransB2Io.
  Definition TransA2B2 := TransAB getTransA2Io getTransB2Io.

  (* (A1+B2) transition can be converted to (A2+B2), B2 stream-io-simulates B1 ->
   * (A1+B1) transition can be converted to (A2+B2) where states match *)
  Section StatesMatch.
    Variable a1: StateA1.
    Variable b1: StateB1.
    Variable sa1b1: Stream TransA1B1 (a1,b1).

    Variable b2: StateB2.
    Variable sb2: Stream TransB2 b2.
    Variable sb2Simulate:
      forall n,
        getStreamIo getTransB1Io n (getStreamB sa1b1) = getStreamIo getTransB2Io n sb2.

    Theorem a1b2IoMatch n:
      getStreamIo getTransA1Io n (getStreamA sa1b1) = getStreamIo getTransB2Io n sb2.
    Proof.
      pose proof streamIoEq sa1b1 n.
      specialize (sb2Simulate n).
      rewrite <- H in *.
      assumption.
    Qed.
      
    Definition sa1b2 := buildTransAB getTransA1Io getTransB2Io (getStreamA sa1b1) sb2
                                     a1b2IoMatch 0.

    Variable convertA1ToA2:
      forall n, TransA2 (getA2FromA1 (fst (fst (getStreamState n sa1b1))))
                        (getA2FromA1 (fst (snd (getStreamState n sa1b1)))).

    Variable notIoEqExistRec:
      forall n,
        getTransA1Io (getStreamATrans sa1b1 n) <> getTransA2Io (convertA1ToA2 n) ->
        {x: TransB2 (fst (getStreamState n sb2)) (snd (getStreamState n sb2))|
         getTransA2Io (convertA1ToA2 n) = getTransB2Io x}.

    Theorem convertA1B2ToA2B2:
      forall n, TransA2B2 (getA2FromA1 (fst (fst (getStreamState n sa1b1))),
                           (fst (getStreamState n sb2)))
                          (getA2FromA1 (fst (snd (getStreamState n sa1b1))),
                           (snd (getStreamState n sb2))).
    Proof.
      intros.
      pose proof (@notIoEqExistRec n) as u1.
      pose proof (decIo (getTransA1Io (getStreamATrans sa1b1 n))
                        (getTransA2Io (convertA1ToA2 n))) as [eq|ne].
      About ABTrans.
      apply (ABTrans getTransA2Io getTransB2Io _ _ (convertA1ToA2 n) _ _
            (getStreamTransition sb2 n)).
      rewrite <- eq.
      pose proof (a1b2IoMatch n).
      unfold getStreamIo in *.
      rewrite <- H.
      pose proof (streamTa n sa1b1).
      unfold getStreamIo in *.
      auto.
      specialize (u1 ne).
      destruct u1 as [x e].
      About ABTrans.
      apply (ABTrans getTransA2Io getTransB2Io _ _ (convertA1ToA2 n) _ _ x e).
    Qed.

    Lemma nextStatesMatch n:
      (getA2FromA1 (fst (snd (getStreamState n sa1b1))),
       (snd (getStreamState n sb2))) =
      (getA2FromA1 (fst (fst (getStreamState (S n) sa1b1))),
       (fst (getStreamState (S n) sb2))).
    Proof.
      pose proof (stateNSndStateSnFst n sa1b1) as u1.
      pose proof (stateNSndStateSnFst n sb2) as u2.
      assert (u3: getA2FromA1 (fst (snd (getStreamState n sa1b1))) =
                  getA2FromA1 (fst (fst (getStreamState (S n) sa1b1))))
             by (do 2 f_equal; intuition).
      f_equal; assumption.
    Qed.

    CoFixpoint buildTransA2B2 n:
      Stream TransA2B2 (getA2FromA1 (fst (fst (getStreamState n sa1b1))),
                        (fst (getStreamState n sb2))) :=
      TCons _ (convertA1B2ToA2B2 n) (eq_rect_r _ (buildTransA2B2 (S n))
                                               (nextStatesMatch n)).

    Lemma a2b2StateMatch' n:
      forall m,
        getA2FromA1 (fst (fst (getStreamState (n+m) sa1b1))) =
        fst (fst (getStreamState n (buildTransA2B2 m))).
    Proof.
      induction n.
      intros.
      reflexivity.

      intros.
      assert (n + S m = S n + m) by omega.
      rewrite <- H.
      specialize (IHn (S m)).
      simpl.
      unfold eq_rect_r, eq_rect, eq_sym.
      match goal with
        | |- _ = fst (fst (getStreamState ?n match ?P with _ => _ end))
          => destruct P
      end.
      assumption.
    Qed.

    Lemma a2b2StateMatch n:
        getA2FromA1 (fst (fst (getStreamState (n) sa1b1))) =
        fst (fst (getStreamState n (buildTransA2B2 0))).
    Proof.
      pose proof (a2b2StateMatch' n 0).
      assert (n+0=n) by omega.
      rewrite H0 in *.
      assumption.
    Qed.

    Theorem statesMatch:
      exists a2 b2 (sa2b2: Stream TransA2B2 (a2,b2)),
        forall n, getA2FromA1 (fst (fst (getStreamState n sa1b1))) =
                  fst (fst (getStreamState n sa2b2)).
    Proof.
      exists (getA2FromA1 (fst (fst (getStreamState 0 sa1b1)))),
      (fst (getStreamState 0 sb2)), (buildTransA2B2 0).
      intros.
      apply (a2b2StateMatch n).
    Qed.
  End StatesMatch.
End ComplexSimulate.

About statesMatch.
