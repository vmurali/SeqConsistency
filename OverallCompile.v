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

  Fixpoint getStreamEq x (sab: Stream TransAB x) n:
    getTransAIo (getStreamTransition n (getStreamA sab)) =
    getTransBIo (getStreamTransition n (getStreamB sab)) :=
    match sab with
      | TCons _ _ (ABTrans _ _ ta _ _ tb eq) sab' =>
        match n as n0 return  with
          | 0 => eq
          | S m => fun _ _ => getStreamEq sab'
        end ta tb
    end.
        match t with
          | ABTrans _ _ ta _ _ tb _ =>
            
            fun sab' => TCons _ ta (getStreamA sab')
        end sab'
    end.


  Section BuildTransAB.
    Variable a: StateA.
    Variable b: StateB.
    Variable sa: Stream TransA a.
    Variable sb: Stream TransB b.
    Variable ioMatch: forall n, getStreamIo getTransAIo n sa = getStreamIo getTransBIo n sb.

    CoFixpoint buildTransAB n:
      Stream TransAB (fst (getStreamState n sa), fst (getStreamState n sb)).
    Proof.
      pose proof (TCons _ (ABTrans (ioMatch n))) as tcons.
      pose proof (stateNSndStateSnFst n sa) as sarew.
      pose proof (stateNSndStateSnFst n sb) as sbrew.
      specialize (buildTransAB (S n)).
      rewrite <- sarew, <- sbrew in buildTransAB.
      apply (tcons buildTransAB).
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

  (* (A1+B2) transition can be converted to (A2+B2), B2 stream-io-simulates B1 ->
   * (A1+B1) transition can be converted to (A2+B2) where states match *)
  Section StatesMatch.
    Variable convertA1B2ToA2B2:
      (forall a1 b2 a1' b2', TransA1B2 (a1, b2) (a1', b2') ->
                             TransA2B2 (getA2FromA1 a1, b2) (getA2FromA1 a1', b2')).
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
      pose proof (getStreamA sa1b1) as sa1.
      pose proof (getStreamB sa1b1) as sb1.
      simpl in *.
      destruct (convertB1ToB2 sb1) as [b2 [sb2 ioMatch]].
      About buildTransAB.
      pose proof (buildTransAB getTransA1Io getTransB2Io sa1 sb2 ioMatch).
      
      
        TransA2B2 (getA2FromA1 a, getB2FromB1 b)
                  (getA2FromA1 a', getB2FromB1 b').
    Proof.
      intros.
      destruct ta.
  Proof.
  End StatesMatch.
    intros.
    True.
    forall a1 b2 a2 b2,
      a
  Theorem complexSimulate:
    TransitionArchSimulate getTransA1Arch getTransA2Arch ->
    StreamIoSimulate getTransB1Io getTransB2Io ->
    StreamArchSimulate
      (@getTransABArchA _ _ _ _ _ _ getTransA1Io getTransB1Io getTransA1Arch)
      (@getTransABArchA _ _ _ _ _ _ getTransA2Io getTransB2Io getTransA2Arch).
  Proof.
    admit.
  Qed.
End ComplexSimulate.
