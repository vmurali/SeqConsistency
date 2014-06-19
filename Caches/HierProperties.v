Require Import Tree DataTypes List Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties Useful Coq.Logic.Classical BaseTree.

Section SubList.
  Context {A: Type}.
  Definition sublist1 (l1 l2: list A) :=
    l1 = tail l2.

  Definition sublist := clos_refl_trans (list A) sublist1.
  Definition sublist' := clos_trans (list A) sublist1.


  Theorem sublistNil: forall {l}, sublist nil l.
  Proof.
    intros l.
    induction l.
    constructor 2.
    constructor 3 with l.
    assumption.
    constructor 1.
    unfold sublist1.
    reflexivity.
  Qed.

  Theorem sublistOfNil': forall {l l2}, sublist l l2 -> l2 = nil -> l = nil.
  Proof.
    intros l l2 sub.
    induction sub.
    intros ynil.
    rewrite ynil in H.
    unfold sublist1 in H.
    simpl in *.
    assumption.
    intuition.
    intros znil.
    firstorder.
  Qed.

  Theorem sublistOfNil: forall {l}, sublist l nil -> l = nil.
  Proof.
    intros l sub.
    pose proof (sublistOfNil' sub).
    assert (@nil A = nil) by reflexivity.
    firstorder.
  Qed.

  Theorem sublistTail: forall {s l}, sublist s l -> s = l \/ sublist s (tl l).
  Proof.
    intros s l sub.
    induction sub.
    right.
    unfold sublist in H.
    unfold sublist1 in H.
    rewrite H.
    constructor 2; assumption.
    left; reflexivity.
    destruct IHsub2.
    rewrite H in *.
    assumption.
    right.
    destruct IHsub1.
    rewrite H0 in *.
    assumption.
    assert (sublist (tl y) y) by (constructor 1; unfold sublist1; reflexivity).
    assert (sublist x y) by (constructor 3 with (tl y); assumption).
    constructor 3 with y; assumption.
  Qed.

  Theorem sublistLength: forall {s1 s2}, sublist s1 s2 -> length s1 <= length s2.
  Proof.
    intros s1.
    induction s1.
    intros s2 sub.
    simpl; omega.
    intros s2 sub.
    pose proof (sublistTail sub) as [eq | neq].
    rewrite eq.
    omega.
    assert (sub2: sublist s1 (tl s2)).
    assert (sub3: sublist s1 (a :: s1)) by (constructor 1; unfold sublist1; reflexivity).
    constructor 3 with (a :: s1); assumption.
    specialize (IHs1 (tl s2) sub2).
    destruct s2.
    simpl in *.
    pose proof (sublistOfNil sub).
    discriminate.
    simpl in IHs1.
    simpl.
    omega.
  Qed.
    
  Theorem hdSublist: forall {l} da {sl}, sublist sl l ->
                                         nth (length l - length sl) l da = hd da sl.
  Proof.
    intros l da.
    induction l.
    intros sl sub.
    pose proof (sublistOfNil sub).
    rewrite H.
    reflexivity.
    intros sl sub.
    pose proof (sublistTail sub) as [eq | neq].
    rewrite eq.
    simpl.
    assert (length l - length l = 0) by omega.
    rewrite H.
    reflexivity.
    simpl in neq.
    specialize (IHl sl neq).
    unfold length.
    fold (length sl).
    fold (length l).
    pose proof (sublistLength neq) as H.
    assert (S (length l) - length sl = S (length l - length sl)) by omega.
    rewrite H0.
    simpl.
    assumption.
  Qed.
End SubList.

Definition descendent' := clos_trans Tree parent.

Theorem descSubsetName: forall {p c},
                          defined p -> descendent c p ->
                          match c, p with
                            | C cx _, C px _ => sublist px cx /\ (c <> p ->
                                                                  length px < length cx)
                          end.
Proof.
  intros p c defp c_p.
  pose proof (treeName2 defp) as namep.

  induction c_p.
  unfold treeNthName in *.
  unfold parent in H.
  destruct y.
  pose proof (in_nth (C nil nil) H) as [i [cond use]].
  specialize (namep i cond).
  rewrite use in namep.
  destruct x.
  rewrite namep.
  constructor.
  constructor 1.
  unfold sublist1.
  reflexivity.

  intros c_ne_p.
  unfold length; fold (length l); omega.

  destruct x.
  constructor.
  constructor 2.
  firstorder.

  pose proof (rt_trans Tree parent y z hier c_p2 defp) as defy.
  destruct (decTree y z).
  rewrite e in *.
  apply (IHc_p1 defp namep).
  destruct (decTree x y).
  rewrite <- e in *.
  apply (IHc_p2 defp namep).
  specialize (IHc_p2 defp namep).
  specialize (IHc_p1 defy (treeName2 defy)).
  destruct x; destruct y; destruct z.
  constructor.
  constructor 3 with l1; intuition.
  destruct IHc_p2 as [_ u2].
  destruct IHc_p1 as [_ u1].
  specialize (u1 n0).
  specialize (u2 n).
  intros.
  omega.
Qed.

Theorem descNonSubsetName:
  forall {p c}, defined p -> defined c -> ~ descendent c p -> ~ descendent p c ->
                match c, p with
                  | C cx _, C px _ => cx <> px
                end.
Proof.
  intros p c defp defc no_c_p no_p_c.
  pose proof (hasFork' no_c_p no_p_c defc defp) as [fork [deff rest]].
  destruct rest as [[d1 [defd1 [d1_f [c_d1 not_p_d1]]]] [d2 [defd2 [d2_f [not_c_d2 p_d2]]]]].
  destruct (decTree d1 d2).
  rewrite e in *.
  firstorder.
  unfold parent in *.
  destruct fork.
  pose proof (in_nth (C nil nil) d1_f) as [i1 [cond1 eq1]].
  pose proof (in_nth (C nil nil) d2_f) as [i2 [cond2 eq2]].
  assert (notSame: i1 <> i2).
  unfold not; intros same.
  rewrite same in *.
  rewrite eq1 in *.
  firstorder.

  pose proof (treeName2 deff i1 cond1) as name1.
  pose proof (treeName2 deff i2 cond2) as name2.
  unfold treeNthName in *.
  remember (C l l0) as fork.

  pose proof (descSubsetName defd1 c_d1) as sub1.
  pose proof (descSubsetName defd2 p_d2) as sub2.

  destruct c; destruct d1; destruct p; destruct d2.
  rewrite eq1 in *; rewrite eq2 in *.

  unfold not; intros eq.
  rewrite eq in sub1.
  destruct sub1 as [u1 _].
  destruct sub2 as [u2 _].

  pose proof (hdSublist 0 u1) as k1.
  pose proof (hdSublist 0 u2) as k2.
  assert (length l3 = length l7).
  rewrite name1; rewrite name2.
  simpl.
  reflexivity.
  rewrite H in k1.
  rewrite k1 in k2.
  rewrite name1 in k2; rewrite name2 in k2.
  simpl in k2.
  intuition.
Qed.

Theorem uniqTreeName: forall {t1 t2}, defined t1 -> defined t2 ->
                                      match t1, t2 with
                                        | C x1 _, C x2 _ => x1 = x2 -> t1 = t2
                                      end.
Proof.
  intros t1 t2 deft1 deft2.
  destruct t1; destruct t2.
  intros x_eq.
  destruct (classic (descendent (C l l0) (C l1 l2))) as [desc | notDesc].
  pose proof (descSubsetName deft2 desc) as whenDesc.
  rewrite x_eq in *.
  destruct whenDesc as [_ sth].
  destruct (decTree (C l1 l0) (C l1 l2)).
  assumption.
  specialize (sth n).
  omega.
  destruct (classic (descendent (C l1 l2) (C l l0))) as [desc | noDesc].
  pose proof (descSubsetName deft1 desc) as whenDesc.
  rewrite x_eq in *.
  destruct whenDesc as [_ sth].
  destruct (decTree (C l1 l0) (C l1 l2)).
  assumption.
  assert (C l1 l2 <> C l1 l0) by auto.
  specialize (sth H).
  omega.
  pose proof (descNonSubsetName deft1 deft2 noDesc notDesc) as nameNeq.
  rewrite x_eq in *.
  firstorder.
Qed.

Theorem uniqParent: forall {c p1 p2}, defined c -> defined p1 -> defined p2 ->
                                      parent c p1 -> parent c p2 -> p1 = p2.
  intros c p1 p2 defc defp1 defp2 c_p1 c_p2.
  unfold parent in *.
  destruct p1, p2.
  pose proof (in_nth (C nil nil) c_p1) as [i1 [cond1 rest1]].
  pose proof (in_nth (C nil nil) c_p2) as [i2 [cond2 rest2]].
  pose proof (treeName2 defp1 i1 cond1) as n1.
  pose proof (treeName2 defp2 i2 cond2) as n2.
  rewrite rest1 in *; rewrite rest2 in *.
  destruct c.
  rewrite n1 in n2.
  injection n2 as use _.
  pose proof (uniqTreeName defp1 defp2) as gd.
  rewrite use in *.
  assert (H: l1 = l1) by reflexivity.
  apply (gd H).
Qed.
