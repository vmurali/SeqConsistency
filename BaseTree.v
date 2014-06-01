Require Import Tree List Omega.

Set Implicit Arguments.

Inductive BaseTree := B: list BaseTree -> BaseTree.

Section ListProp.
  Variable A: Type.
  Variable def: A.
  Theorem appLastNth: forall l i a, i = length l -> nth i (l ++ (a :: nil)) def = a.
  Proof.
    intros l.
    induction l.
    intros i a i_len.
    simpl in *.
    rewrite i_len.
    auto.
    intros i a0 i_len.
    unfold length in i_len.
    fold (length l) in i_len.
    rewrite i_len.
    unfold app.
    fold (app l (a0 :: nil)).
    simpl.
    specialize (IHl (length l) a0).
    assert (length l = length l) by auto.
    specialize (IHl H).
    assumption.
  Qed.

  Theorem appNotLastNth: forall l i a, i < length l -> nth i (l ++ (a :: nil)) def = nth i l def.
  Proof.
    intros l.
    induction l.
    intros i a i_len.
    simpl in *.
    omega.
    intros i a0 i_len.
    unfold app.
    fold (app l (a0::nil)).
    destruct i.
    simpl.
    auto.
    simpl.
    simpl in i_len.
    assert (i < length l) by omega.
    specialize (IHl i a0 H).
    assumption.
  Qed.

  Theorem appLen: forall (l: list A) a, length (l ++ a :: nil) = S (length l).
  Proof.
    intros l a.
    induction l.
    simpl.
    auto.
    unfold app.
    fold (app l (a :: nil)).
    simpl.
    omega.
  Qed.

  Theorem revLen: forall (l: list A), length l = length (rev l).
  Proof.
    intros l.
    induction l.
    simpl.
    auto.
    simpl.
    pose proof (appLen (rev l) a).
    rewrite H; clear H.
    omega.
  Qed.

  Theorem revProp: forall l i, i < length l -> nth i l def = nth (length l - S i) (rev l) def.
  Proof.
    intros l.
    induction l.
    intros i i_lt_len.
    simpl in *.
    omega.
    intros i i_lt_len.
    unfold rev.
    fold (rev l).
    unfold length.
    fold (length l).
    assert (S (length l) - S i = (length l) - i) by omega.
    rewrite H.
    clear H.
    destruct i.
    simpl.
    assert (length l - 0 = length l) by omega.
    rewrite H; clear H.
    pose proof (revLen l) as H.
    rewrite H; clear H.
    assert (length (rev l) = length (rev l)) by reflexivity.
    pose proof (appLastNth _ a H).
    rewrite H0.
    auto.
    simpl in i_lt_len.
    pose proof (revLen l) as H.
    assert (length l - S i < length (rev l)) by omega.
    pose proof (appNotLastNth _ a H0).
    rewrite H1.
    simpl.
    assert (i < length l) by omega.
    specialize (IHl i H2).
    assumption.
  Qed.

  Section EqLen.
    Context (l: list A).
    Context {B: Type}.
    Context (f: A -> list A -> B).
    Fixpoint trans ls :=
      match ls with
        | nil => nil
        | x :: xs => f x xs :: trans xs
      end.
    Theorem eqLen: length (trans l) = length l.
    Proof.
      induction l.
      simpl.
      reflexivity.
      simpl.
      f_equal.
      assumption.
    Qed.
  End EqLen.
End ListProp.

Section Strange.
  Variable (nm: list nat).

  Fixpoint mkNameList ls :=
    match ls with
      | nil => nil
      | x :: xs => (C (length xs :: nm) x) :: mkNameList xs
    end.

  Theorem mkNameListLength ls: length (mkNameList ls) = length ls.
  Proof.
    induction ls.
    simpl.
    auto.
    simpl.
    f_equal.
    auto.
  Qed.

  Theorem posValue: forall ls i, i < length ls -> match nth i (mkNameList ls) (C nil nil) with
                                                      | C x _ => x = (length ls - S i) :: nm
                                                    end.
  Proof.
    intros ls.
    induction ls.
    intros i i_lt_l.
    simpl in i_lt_l.
    omega.
    intros i i_lt_l.
    simpl in i_lt_l.
    unfold mkNameList.
    fold mkNameList.
    destruct i.
    simpl.
    assert (H: length ls - 0 = length ls) by omega.
    rewrite H; clear H.
    auto.
    simpl.
    assert (H: i < length ls) by omega.
    apply (IHls i H).
  Qed.

  Theorem posValueRev': forall ls i, i < length ls ->
                                       match nth (length ls - S i) (rev (mkNameList ls)) (C nil nil) with
                                         | C x _ => x = (length ls - S i) :: nm
                                       end.
  Proof.
    intros ls i i_lt_n.
    pose proof (posValue _ i_lt_n) as gdOne.
    pose proof (mkNameListLength ls) as t1.
    rewrite <- t1 in i_lt_n.
    pose proof (revProp (C nil nil) _ i_lt_n) as bdOne.
    rewrite t1 in bdOne.
    rewrite bdOne in gdOne.
    auto.
  Qed.

  Theorem posValueRev: forall ls i, i < length ls ->
                                      match nth i (rev (mkNameList ls)) (C nil nil) with
                                        | C x _ => x = i :: nm
                                      end.
  Proof.
    intros ls i i_lt_n.
    assert (sth: length ls - S i < length ls) by omega.
    pose proof (posValueRev' _ sth) as sth2.
    assert (H: length ls - S (length ls - S i) = i) by omega.
    rewrite H in sth2.
    assumption.
  Qed.
End Strange.

Fixpoint getCs nm b :=
  match b with
    | B bs => rev (mkNameList nm
                              ((fix addC bs :=
                                  match bs with
                                    | nil => nil
                                    | b' :: bs' => getCs (length bs' :: nm) b' :: addC bs'
                                  end) bs))
  end.

Definition getC nm b := C nm (getCs nm b).

Theorem parentTreeName c p np bp: parent c p ->
                                  p = getC np bp ->
                                  exists nc bc, c = getC nc bc.
Proof.
  intros c_p pEq.
  unfold parent in *; unfold getC in *.
  destruct p.
  injection pEq as lEqNp l0Eq.
  rewrite lEqNp in *; rewrite l0Eq in *; clear lEqNp l0Eq.
  clear pEq.
  destruct bp.
  simpl in c_p.
  pose proof @In_rev as sth.
  assert (In_rev: forall A l (x: A), In x (rev l) -> In x l) by
         (generalize sth; clear;
          intros sth A l x inl; specialize (sth A l x);
          destruct sth;
          intuition); clear sth.
  pose proof (In_rev _ _ _ c_p) as inp; clear In_rev c_p l0 l.
  induction l1.
  simpl in *.
  intuition.
  simpl in inp.
  pose proof (eqLen l1 (fun x y => getCs (length y :: np) x)) as sth.
  unfold trans in sth.
  rewrite sth in inp.
  destruct inp.
  exists (length l1 :: np); exists a; auto.
  specialize (IHl1 H).
  assumption.
Qed.

Theorem treeNameHelp nm b:
  match getC nm b with
    | C x ls => treeNthName x ls
  end.
Proof.
  unfold treeNthName.
  unfold getC.
  destruct b.
  simpl.
  intros n n_lt_len.
  apply posValueRev.
  remember  ((fix addC (bs : list BaseTree) : list (list Tree) :=
         match bs with
         | nil => nil
         | b' :: bs' => getCs (length bs' :: nm) b' :: addC bs'
         end) l) as sth.
  clear Heqsth.
  pose proof (mkNameListLength nm sth) as H.
  pose proof (revLen (mkNameList nm sth)) as H0.
  rewrite H in H0.
  rewrite <- H0 in n_lt_len.
  assumption.
Qed.

Theorem descImpGetc p c: descendent c p ->
                         (exists np bp, p = getC np bp) ->
                         exists nc bc, c = getC nc bc.
Proof.
  intros desc.
  induction desc.
  intros [np [bp pEq]].
  apply (parentTreeName _ H pEq).
  intros [np [bp pEq]].
  exists np; exists bp; intuition.
  intros use.
  specialize (IHdesc2 use).
  specialize (IHdesc1 IHdesc2).
  assumption.
Qed.
