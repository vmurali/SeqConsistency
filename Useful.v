Require Import Omega List.

Set Implicit Arguments.

Definition classicalProp P := P \/ ~ P.

Ltac applyExists :=
  match goal with
    | H: exists _, _ |- _ => let x := fresh in
                               let y := fresh in
                                 destruct H as [x y]; exists x
  end.

Ltac destructAll :=
  match goal with
    | [|- context [match ?P with _ => _ end] ] => destruct P
    | [_:context [match ?P with _ => _ end] |- _] => destruct P
  end.

Ltac diff t1 t2 cond :=
  remember (t2 - t1) as td eqn:Heqtd;
  assert (t2eq: t2 = t1 + td) by omega;
  rewrite t2eq in *; clear t2eq Heqtd t2 cond.

Ltac simplArith :=
  repeat match goal with
           | [|- context [?x + 0]] => assert (H: x+0 = x) by omega; rewrite H; clear H
           | [|- context [?x + S ?y]] => assert (H: x+S y = S(x+y)) by omega; rewrite H; clear H
           | [H: context [?x + 0] |- _ ] => assert (L: x+0=x) by omega; rewrite L in H; clear L
           | [H: context [?x + S ?y]|- _ ] => assert (L: x+S y=S(x+y)) by omega; rewrite L in H; clear L
         end.
                                                                   

Section StrongInd1.
  Variable P: nat -> Type.
  Hypothesis case_0: P 0.
  Hypothesis case_n: forall t, (forall ti, ti <= t -> P ti) -> P (S t).

  Theorem strong_ind' t: P t.
  Proof.
    assert (q0: forall ti, ti <= 0 -> P ti) by 
        (intros ti ti_le_0; assert (rew: ti = 0) by omega; rewrite rew; assumption).
    assert (qIHt: forall t, (forall ti, ti <= t -> P ti) -> (forall ti, ti <= S t -> P ti)).
    intros t0 lt_t0.
    specialize (case_n lt_t0).
    intros ti ti_le_S_t0.
    pose proof (le_lt_eq_dec ti (S t0) ti_le_S_t0) as options.
    destruct options as  [hyp|new].
    firstorder.
    rewrite new.
    assumption.
    assert (Hyp: forall t, (forall ti, ti <= t -> P ti)) by (
                                                            induction t0; firstorder).
    specialize (Hyp t t).
    assert (fct: t <= t) by omega.
    firstorder.
  Qed.
End StrongInd1.

Section StrongInd2.
  Variable P: nat -> Type.
  Hypothesis case_n: forall t, (forall ti, ti < t -> P ti) -> P t.
  Theorem strong_ind t: P t.
  Proof.
    assert (case0: P 0).
    specialize (@case_n 0).
    assert (ez: forall ti, ti < 0 -> P ti) by (intros ti cond; assert False by omega;
                                               intuition).
    apply (@case_n ez).
    assert (casen: forall t, (forall ti, ti <= t -> P ti) -> P (S t)).
    intros t0 cond.
    assert (cond2: forall ti, ti < S t0 -> P ti) by (intros ti cond2;
                                                     assert (ti <= t0) by omega;
                                                     intuition).
    apply (case_n cond2).
    apply (strong_ind' _ case0 casen t).
  Qed.
End StrongInd2.

Section List.
  Variable A: Set.
  Variable P: A -> Prop.
  Variable ls: list A.

  Hypothesis exOrNot: forall x, In x ls -> P x \/ ~ P x.

  Theorem exOrNotforall:
    (exists x, In x ls /\ P x) \/ forall x, In x ls -> ~ P x.
  Proof.
    induction ls.
    intuition.
    simpl in *.
    assert (H: forall x, In x l -> P x \/ ~ P x).
    intros x inxl.
    assert (arg: a = x \/ In x l) by intuition.
    apply (exOrNot _ arg).
    specialize (IHl H).
    destruct IHl.
    destruct H0 as [x inxl px].
    left.
    exists x.
    intuition.
    assert (arg: a = a \/ In a l) by intuition.
    specialize (exOrNot a arg).
    destruct exOrNot.
    left.
    exists a.
    intuition.
    right.
    unfold not.
    intros x cond px.
    destruct cond.
    rewrite H2 in *.
    intuition.
    apply (H0 _ H2 px).
  Qed.
End List.