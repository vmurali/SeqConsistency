Require Import Rules DataTypes Omega Useful List Coq.Logic.Classical.
Import mkDataTypes.

Theorem enqGreater':
  forall {s p c t i}, In i (labelCh t s p c) -> t > i.
Proof.
  intros s p c t i inI.
  induction t.
  unfold labelCh in *.
  unfold In in inI.
  intuition.
  unfold labelCh in inI; fold labelCh in inI.
  destruct (trans oneBeh t).
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  specialize (IHt inI); omega.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  destruct (decTree c p0).
  destruct (decTree p c0).
  pose proof (notInRemove i (labelCh t rch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree c p0).
  destruct (decTree p c0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  destruct (decTree c c0).
  destruct (decTree p p0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.


  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold In in inI.
  destruct inI as [mu1|mu2]; [ | specialize (IHt mu2)]; omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  pose proof (notInRemove i (labelCh t mch p c) inI) as f.
  specialize (IHt f); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
  specialize (IHt inI); omega.
Qed.


Theorem posGreater:
  forall {s p c t n},
    n < length (labelCh t s p c) ->
    forall {i}, i < n ->
                nth n (labelCh t s p c) 0 < nth i (labelCh t s p c) 0.
Proof.
  intros s p c t.
  induction t.
  intros n n_lt i i_lt.
  unfold labelCh in n_lt.
  simpl in n_lt.
  assert False by omega; intuition.

  intros n n_lt i i_lt.
  unfold labelCh in n_lt; fold labelCh in n_lt. unfold labelCh; fold labelCh.

  assert (one: n < length (t :: labelCh t s p c) ->
               nth n (t :: labelCh t s p c) 0 < nth i (t :: labelCh t s p c) 0).
  intros n_lt'.
  destruct n.
  assert False by omega; intuition.
  assert (n_lt'': n < length (labelCh t s p c)) by
      (unfold length in n_lt'; fold (length (labelCh t s p c)) in n_lt'; omega).
  unfold nth.
  fold (nth n (labelCh t s p c) 0).
  destruct i.
  pose proof (enqGreater' (nth_In (labelCh t s p c) 0 n_lt'')).
  assumption.
  assert (H: i < n) by omega.
  apply (IHt n n_lt'' i H).

  destruct (trans oneBeh t).

  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  specialize (IHt n n_lt i i_lt); assumption.
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct (decTree c p0).
  destruct (decTree p c0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree c p0).
  destruct (decTree p c0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.  
  destruct (decTree c c0).
  destruct (decTree p p0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  apply (one n_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.

  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  apply (listNoShift IHt n_lt i_lt).
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
  specialize (IHt n n_lt i i_lt); assumption.
Qed.

Theorem msgIdTime: forall {s p c m t}, mark s p c t m -> msgId m = t.
Proof.
  intros s p c m t markm.
  unfold mark in markm.
  destruct (trans oneBeh t);intuition.
Qed.

Theorem enqGreater: forall {s p c m t i s'}, mark s p c t m ->
                                             In i (labelCh t s' p c) -> msgId m > i.
Proof.
  intros s p c m t i s' markm ini.
  pose proof (enqGreater' ini) as H.
  pose proof (msgIdTime markm).
  rewrite H0.
  assumption.
Qed.

Theorem lenEq: forall {s p c t}, length (ch (sys oneBeh t) s p c) = length (labelCh t s p c).
Proof.
  intros s p c t.
  induction t.
  unfold labelCh.
  pose proof (init oneBeh) as initi.
  rewrite initi.
  unfold initGlobalState; reflexivity.
  unfold labelCh; fold labelCh.
  destruct (trans oneBeh t).
  assumption.
  assumption.
  simpl.
  destruct s.
  assumption.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  unfold length; f_equal; assumption.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  unfold length; f_equal; assumption.
  intuition.
  destruct (decTree c c0); intuition.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) rch p c) (labelCh t rch p c) IHt).
  intuition.
  destruct (decTree c p0); intuition.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  unfold length; intuition.
  intuition.
  intuition.
  intuition.



  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  unfold length; intuition.
  destruct (decTree c p).
  rewrite <- e0 in *.
  destruct (decTree c p0);
  intuition.
  intuition.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  destruct (decTree c p).
  rewrite <- e2 in *.
  intuition.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  destruct (decTree c p);
  intuition.
  destruct (decTree c p0).
  intuition.
  destruct (decTree c c0); intuition.
  intuition.
  


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  intuition.
  intuition.
  intuition.


  simpl in *.
  destruct s.
  destruct (decTree p c0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c p0) as [y|ny].
  rewrite <- y in *.
  unfold length; intuition.
  intuition.
  intuition.
  intuition.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [y|ny].
  rewrite <- y in *.
  apply (eqLen (ch (sys oneBeh t) mch p c) (labelCh t mch p c) IHt).
  intuition.
  intuition.
  intuition.
Qed.

Theorem inImpSend: forall {s p c b l t},
                     In (b, l) (combine (ch (sys oneBeh (S t)) s p c)
                                        (labelCh (S t) s p c)) ->
                     ~ In (b, l) (combine (ch (sys oneBeh t) s p c)
                                          (labelCh t s p c)) ->
                     mark (type b) p c t (Build_Mesg (fromB b) (toB b) (addrB b)
                                                     (dataBM b) l) /\
                     (combine (ch (sys oneBeh (S t)) s p c) (labelCh (S t) s p c)) =
                     (b,l) :: (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)).
Proof.
  intros s p c b l t inComb notInComb.
  unfold mark; simpl in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  simpl in *.
  destruct s. intuition.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) p a;
                          toB := x;
                          addrB := a;
                          dataBM := initData zero; type := rch |}, t)) by intuition.
  pose proof (eachProd L) as [L1 L2].
  rewrite L1; rewrite L2; simpl; intuition.
  intuition.
  intuition.



  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) rch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  destruct s.
  destruct (decTree p p0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c c0) as [cEq | cNeq].
  rewrite <- cEq in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := dirSt (sys oneBeh t) p c a;
                          toB := toB r;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) p a; type := mch |}, t)) by intuition.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; intuition.
  intuition.
  destruct (decTree c c0) as [easy|hard]; intuition.

  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  pose proof (removeCombine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
    as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) rch p c) (labelCh t rch p c))
                          inComb) as H.
  intuition.
  intuition.
  destruct (decTree c p0) as [ez|hd]; intuition.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c))
                          inComb) as H.
  intuition.
  intuition.
  intuition.
  intuition.


  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [yay|nay].
  rewrite <- yay in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := dirSt (sys oneBeh t) p c a;
                          toB := x;
                          addrB := a;
                          dataBM := initData zero; type := rch |}, t)) by intuition.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto;
    rewrite <- rew in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite cEq in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) c0 a;
                          toB := toB r;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) c0 a; type := mch |}, t)) by intuition.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; intuition.
  destruct (decTree c c0) as [ceq | cneq].
  destruct (decTree c0 p0) as [peq | pneq].
  rewrite <- pEq in *; rewrite ceq in *; rewrite peq in *.
  intuition.
  intuition.
  intuition.
  destruct (decTree p p0) as [ez|hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [mu|su].
  rewrite <- mu in *.
  destruct (decTree c p) as [alf|bet].
  rewrite alf in *.
  intuition.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as sthEq.
  rewrite <- sthEq in inComb.
  pose proof (notInRemove (b, l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c))
                          inComb) as H.
  intuition.
  destruct (decTree c p) as [yes|no]; intuition.

  destruct (decTree c p0).
  intuition.
  destruct (decTree c c0);
  intuition.
  intuition.
  

  simpl in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
  intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p c0) as [pEq | pNeq].
  rewrite <- pEq in *.
  destruct (decTree c p0) as [cEq | cNeq].
  rewrite <- cEq in *.
  unfold combine in inComb.
  unfold In in inComb.
  assert (L: (b, l) = ({|
                          fromB := st (sys oneBeh t) p a;
                          toB := x;
                          addrB := a;
                          dataBM := dt (sys oneBeh t) p a; type := mch |}, t)) by intuition.
  pose proof (eachProd L) as [L1 L2]; clear L.
  rewrite L1; rewrite L2; simpl; intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0) as [ez | hd].
  rewrite <- ez in *.
  destruct (decTree c c0) as [m1 | m2].
  rewrite <- m1 in *.
  pose proof (removeCombine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) as H.
  rewrite <- H in inComb.
  pose proof (notInRemove (b,l) (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)) inComb) as H2.
  intuition.
  intuition.
  intuition.
  intuition.
Qed.

  Theorem lastByRemove: forall {b l ty src dst t},
                          ~ In (b, l)
                            (combine (removelast (ch (sys oneBeh t) ty src dst))
                                     (removelast (labelCh t ty src dst))) ->
                          In (b, l) (combine (ch (sys oneBeh t) ty src dst)
                                             (labelCh t ty src dst)) ->
                          type b = type (last (ch (sys oneBeh t) ty src dst) dmy) /\
                          fromB b = fromB (last (ch (sys oneBeh t) ty src dst) dmy) /\
                          toB b = toB (last (ch (sys oneBeh t) ty src dst) dmy) /\
                          addrB b = addrB (last (ch (sys oneBeh t) ty src dst) dmy) /\
                          dataBM b = dataBM (last (ch (sys oneBeh t) ty src dst) dmy) /\
                          l = last (labelCh t ty src dst) 0 /\
                          combine (removelast (ch (sys oneBeh t) ty src dst))
                                  (removelast (labelCh t ty src dst)) =
                          removelast (combine (ch (sys oneBeh t) ty src dst)
                                              (labelCh t ty src dst)).
  Proof.
    intros b l ty src dst t notIn isIn.
    pose proof (removeCombine (ch (sys oneBeh t) ty src dst) (labelCh t ty src dst)) as dist.
    rewrite <- dist in notIn.
    pose proof (inNotInRemove (dmy, 0) isIn notIn) as bLast.
    pose proof (lastCombineDist _ dmy _ 0 (@lenEq ty src dst t)) as dist2.
    rewrite dist2 in bLast.
    pose proof (eachProd bLast) as [bEq lEq].
    rewrite bEq in *; rewrite lEq in *.
    pose proof (removeCombine (ch (sys oneBeh t) ty src dst)
                              (labelCh t ty src dst)) as dist3.
    rewrite dist3.
    constructor; intuition.
  Qed.

Theorem notInImpRecv: forall {s p c b l t},
                     ~ In (b, l) (combine (ch (sys oneBeh (S t)) s p c)
                                        (labelCh (S t) s p c)) ->
                     In (b, l) (combine (ch (sys oneBeh t) s p c)
                                          (labelCh t s p c)) ->
                     recv (type b) p c t (Build_Mesg (fromB b) (toB b) (addrB b)
                                                     (dataBM b) l) /\
                     (combine (ch (sys oneBeh (S t)) s p c) (labelCh (S t) s p c)) =
                     removelast (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)).
Proof.
  intros s p c b l t notIn isIn.
  unfold recv. unfold labelCh in *; fold labelCh in *.
  simpl.

  destruct (trans oneBeh t).
  simpl in *. intuition.
  simpl in *; intuition.


  simpl in *.
  destruct s.
  intuition.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold combine in notIn.
  unfold In in notIn.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  unfold combine in notIn.
  unfold In in notIn.
  intuition.
  intuition.
  destruct (decTree p p0); intuition.
  destruct (decTree p c0).
  destruct (decTree c p0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  pose proof (lastByRemove notIn isIn) as u.
  intuition.
  intuition.
  destruct (decTree c p0);
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  pose proof (lastByRemove notIn isIn) as u.
  intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  unfold combine in notIn.
  unfold In in notIn.
  intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  unfold combine in notIn.
  unfold In in notIn.
  intuition.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  destruct (decTree p p0).
  rewrite <- e2 in *.
  assert (c = p) by auto; intuition.
  intuition.
  intuition.
  destruct (decTree p p0).
  destruct (decTree c c0).
  destruct (decTree c p0).
  rewrite <- e0 in *; rewrite <- e1 in *; rewrite <- e2 in *.
  intuition.
  rewrite <- e0 in *; rewrite <- e1 in *.
  pose proof (lastByRemove notIn isIn) as u.
  intuition.
  destruct (decTree c p0); intuition.
  destruct (decTree c p0); destruct (decTree c c0); intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  pose proof (lastByRemove notIn isIn) as u.
  intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold combine in notIn.
  unfold In in notIn.
  intuition.
  intuition.
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  rewrite <- e0 in *; rewrite <- e1 in *.
  pose proof (lastByRemove notIn isIn) as u.
  intuition.
  intuition.
  intuition.
  intuition.
Qed.

Theorem notInImpExRecv:
  forall {s p c b l t1 t2}, t1 < t2 ->
                            ~ In (b, l) (combine (ch (sys oneBeh t2) s p c)
                                                 (labelCh t2 s p c)) ->
                            In (b, l) (combine (ch (sys oneBeh t1) s p c)
                                               (labelCh t1 s p c)) ->
                            exists t, t1 <= t < t2 /\ recv (type b) p c t
                                           (Build_Mesg (fromB b) (toB b) (addrB b)
                                                       (dataBM b) l) /\
                                      (combine (ch (sys oneBeh (S t)) s p c)
                                               (labelCh (S t) s p c)) =
                                      removelast (combine (ch (sys oneBeh t) s p c)
                                                          (labelCh t s p c)).
Proof.
  intros s p c b l t1 t2 cond notIn isIn.
  remember (t2 - t1 - 1) as td.
  assert (t2 = t1 + S td) by omega.
  rewrite H in *; clear cond Heqtd H.
  induction td.
  assert (t1 + 1 = S t1) by omega.
  rewrite H in *.
  exists t1.
  assert (t1 <= t1 < S t1) by omega.
  pose proof (notInImpRecv notIn isIn); intuition.
  destruct (classic (In (b, l) (combine (ch (sys oneBeh (t1 + S td)) s p c)
                                        (labelCh (t1 + S td) s p c)))) as [same|diff].
  assert (t1 + S (S td) = S (t1 + S td)) by omega.
  rewrite H in *.
  exists (t1 + S td).
  pose proof (notInImpRecv notIn same); intuition.
  specialize (IHtd diff).
  destruct IHtd as [t [cond rest]].
  assert (t1 <= t1 + S td < t1 + S (S td)) by omega.
  exists t.
  intuition.
Qed.

Theorem enqImpIn: forall {s p c t m}, mark s p c t m ->
                                      In
                                        (Build_BaseMesg (from m) (to m) (addr m) (dataM m)
                                                        s, msgId m)
                                        (combine (ch (sys oneBeh (S t)) (markc t) p c)
                                                 (labelCh (S t) (markc t) p c)).
Proof.
  intros s p c t m markm.
  unfold mark in markm. unfold labelCh; fold labelCh. unfold markc in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  simpl.
  destruct markm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  destruct s.
  discriminate.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold combine; unfold In; left.
  rewrite <- u1 in *; rewrite <- u2 in *;
  rewrite <- u4 in *. rewrite u5 in *; rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  reflexivity.
  assert (c = p0) by auto; intuition.
  assert (p = c0) by auto; intuition.

  simpl.
  destruct markm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  destruct s.
  destruct (decTree p p0).
  destruct (decTree c c0).
  unfold combine; unfold In; left.
  fold r in u4; fold a in u4.
  fold r in u6; fold a in u6.
  rewrite <- u1 in *; rewrite <- u2 in *;
  rewrite <- u4 in *. rewrite u5 in *; rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  reflexivity.
  assert (c = c0) by auto; intuition.
  assert (p = p0) by auto; intuition.
  discriminate.

  intuition.

  simpl.
  destruct markm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  destruct s.
  discriminate.
  destruct (decTree p p0).
  destruct (decTree c c0).
  unfold combine; unfold In; left.
  rewrite <- u1 in *; rewrite <- u2 in *;
  rewrite <- u4 in *. rewrite u5 in *; rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  reflexivity.
  assert (c = c0) by auto; intuition.
  assert (p = p0) by auto; intuition.

  simpl.
  destruct markm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  fold r in u4; fold a in u4.
  fold r in u6; fold a in u6.  
  unfold combine; unfold In; left.
  rewrite <- u1 in *; rewrite <- u2 in *;
  rewrite <- u4 in *. rewrite u5 in *; rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  reflexivity.
  assert (c = p0) by auto; intuition.
  assert (p = c0) by auto; intuition.
  discriminate.

  intuition.

  simpl.
  destruct markm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  destruct s.
  destruct (decTree p c0).
  destruct (decTree c p0).
  unfold combine; unfold In; left.
  rewrite <- u1 in *; rewrite <- u2 in *;
  rewrite <- u4 in *. rewrite u5 in *; rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  reflexivity.
  assert (c = p0) by auto; intuition.
  assert (p = c0) by auto; intuition.
  discriminate.

  intuition.
Qed.

Theorem noEnqMR: forall {p c t m r}, mark mch p c t m -> mark rch p c t r -> False.
Proof.
  intros p c t m r send1 send2.
  unfold mark in *; destruct (trans oneBeh t).
  intuition.
  intuition.
  destruct send1 as [_ [_ [u _]]]; discriminate.
  destruct send2 as [_ [_ [u _]]]; discriminate.
  intuition.
  destruct send1 as [_ [_ [u _]]]; discriminate.
  destruct send2 as [_ [_ [u _]]]; discriminate.
  intuition.
  destruct send2 as [_ [_ [u _]]]; discriminate.
  intuition.
Qed.

Theorem inImpSent: forall {s p c b l t1 t2}, t1 < t2 ->
                     In (b, l) (combine (ch (sys oneBeh t2) s p c) (labelCh t2 s p c)) ->
                     ~ In (b, l) (combine (ch (sys oneBeh t1) s p c) (labelCh t1 s p c)) ->
                     exists ti, t1 <= ti < t2 /\ mark (type b) p c ti
                                                      (Build_Mesg (fromB b) (toB b)
                                                                  (addrB b) (dataBM b) l) /\
                     (combine (ch (sys oneBeh (S ti)) s p c) (labelCh (S ti) s p c)) =
                     (b,l) :: (combine (ch (sys oneBeh ti) s p c) (labelCh ti s p c)).
Proof.
  intros s p c b l t1 t2 cond isIn notIn.
  remember (t2 - t1 - 1) as td.
  assert (t2 = t1 + S td) by omega.
  rewrite H in *; clear Heqtd H cond.
  induction td.
  assert (rew: t1 + 1 = S t1) by omega.
  rewrite rew in *; clear rew.
  assert (cond2: t1 <= t1 < S t1) by omega.
  pose proof (inImpSend isIn notIn) as use.
  exists t1; generalize cond2 use; clear.
  constructor; assumption.
  destruct (classic (In (b, l) (combine (ch (sys oneBeh (t1 + S td)) s p c)
                                        (labelCh (t1 + S td) s p c)))) as
      [easy | hard].
  destruct (IHtd easy) as [ti [cond use]].
  assert (ez: t1 <= ti < t1 + S (S td)) by omega.
  generalize ez use; clear.
  intros; exists ti; constructor; assumption.
  assert (h: t1 + S (S td) = S (t1 + S td)) by omega.
  rewrite h in *; clear h.
  pose proof (inImpSend isIn hard) as use.
  exists (t1 + S td).
  assert (t1 <= t1 + S td < S ( t1 + S td)) by omega.
  generalize H use; clear; intros; constructor; assumption.
Qed.

Theorem inImpSent2: forall {s p c b l t},
                      In (b, l) (combine (ch (sys oneBeh t) s p c) (labelCh t s p c)) ->
                      exists ti, ti < t /\ mark (type b) p c ti
                                    (Build_Mesg (fromB b) (toB b) (addrB b) (dataBM b) l) /\
                                    (combine (ch (sys oneBeh (S ti)) s p c) (labelCh (S ti) s p c)) =
                                 (b, l) :: combine (ch (sys oneBeh ti) s p c) (labelCh ti s p c).
Proof.
  intros s p c b l t isIn.
  assert (zero: ~ In (b, l) (combine (ch (sys oneBeh 0) s p c) (labelCh 0 s p c))).
  pose proof (init oneBeh).
  rewrite H.
  unfold initGlobalState.
  simpl.
  intuition.
  destruct t.
  intuition.
  assert (0 < S t) by omega.
  pose proof (inImpSent H isIn zero) as [ti [cond rest]].
  assert (ti < S t) by omega.
  exists ti.
  intuition.
Qed.
  
Theorem recvImpIn: forall {s p c m t},
                     recv s p c t m ->
                     In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s,
                         msgId m) (combine (ch (sys oneBeh t) (recvc t) p c)
                                             (labelCh t (recvc t) p c)).
Proof.
  unfold recv.
  intros s p c m t recvm. unfold recvc.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq rch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = 
               last (ch (sys oneBeh t) rch c0 p0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) rch c0 p0) dmy); simpl in *; reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t rch c0 p0) 0 H use5) as almost.
  assumption.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
  intuition.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch c0 p0) dmy) by (
                rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
                destruct (last (ch (sys oneBeh t) mch c0 p0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                               (labelCh t mch c0 p0) 0 H use5) as almost.
  assumption.
  intuition.
  destruct recvm as [u1 [u2 [u3 [use1 [use2 [use3 [use4 use5]]]]]]].
  pose proof (@lenEq mch p c t) as H.
  rewrite <- u1 in *; rewrite <- u2 in *.
  assert (lft: Build_BaseMesg (from m) (to m) (addr m) (dataM m) s = last (ch (sys oneBeh t) mch p0 c0) dmy) by (
            rewrite use1; rewrite use2; rewrite use3; rewrite use4; rewrite u3;
            destruct (last (ch (sys oneBeh t) mch p0 c0) dmy); reflexivity).
  pose proof (lenEqLastCombine _ _ dmy n lft (msgId m)
                                    (labelCh t mch p0 c0) 0 H use5) as almost.
  assumption.
Qed.

Theorem recvImpSend': forall {s p c m t}, recv s p c t m -> exists t', t' < t /\ send s p c t' m.
Proof.
  intros s p c m t recvm.
  pose proof (recvImpIn recvm) as gdIn.
  destruct t.
  pose proof (init oneBeh) as sth.
  rewrite sth in *; clear sth.
  unfold initGlobalState in *; simpl in *.
  intuition.
  assert (sth: 0 < S t) by omega.
  assert (sth3: ~ In ({|
            fromB := from m;
            toB := to m;
            addrB := addr m;
            dataBM := dataM m;
            type := s |}, msgId m)
            (combine (ch (sys oneBeh 0) (recvc (S t)) p c)
                     (labelCh 0 (recvc (S t)) p c))).
  pose proof (init oneBeh) as sth2.
  rewrite sth2 in *; clear sth2.
  unfold initGlobalState; simpl.
  unfold not; intro; assumption.
  pose proof (inImpSent sth gdIn sth3) as [ti [cond rest]].
  simpl in *.
  exists ti.
  assert (ti < S t) by omega.
  unfold send.
  destruct rest as [useful _].
  assert (great: mark s p c ti m).
  destruct m.
  simpl in *.
  assumption.
  constructor; assumption.
Qed.

Theorem recvImpSend: forall {s p c m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
Proof.
  intros s p c m t recvm.
  pose proof recvImpSend' recvm as [t' [cond sendm]].
  assert (t' <= t) by omega.
  exists t'; intuition.
Qed.

Theorem enqC2P: forall {s p c t}, parent c p -> ch (sys oneBeh t) s c p <> nil ->
                                  type (last (ch (sys oneBeh t) s c p) dmy) = s.
Proof.
  intros s p c t c_p notNil.
  assert (gd: last (ch (sys oneBeh t) s c p) dmy = fst (last (combine (ch (sys oneBeh t) s c p)                                                                  (labelCh t s c p)) (dmy, 0)))
  by apply (lastCombine dmy 0 (@lenEq s c p t)).
  rewrite gd; clear gd.
  assert (gd2: combine (ch (sys oneBeh t) s c p) (labelCh t s c p) <> nil).
  pose proof (@lenEq s c p t) as gd.
  destruct (ch (sys oneBeh t) s c p).
  intuition.
  destruct (labelCh t s c p).
  simpl in *.
  discriminate.
  simpl.
  unfold not; intros; discriminate.
  intuition.
  pose proof (@lastIn (BaseMesg * nat) (combine (ch (sys oneBeh t) s c p) (labelCh t s c p))
             (dmy, 0) gd2) as use.
  destruct t.
  pose proof (init oneBeh) as sth.
  rewrite sth in *; clear sth.
  unfold initGlobalState in *; simpl in *.
  intuition.
  assert (sth: 0 < S t) by omega.
  assert (sth3: ~ In (last (combine (ch (sys oneBeh (S t)) s c p) (labelCh (S t) s c p))
             (dmy, 0))
            (combine (ch (sys oneBeh 0) s c p)
                     (labelCh 0 s c p))).
  pose proof (init oneBeh) as sth2.
  rewrite sth2 in *; clear sth2.
  unfold initGlobalState; simpl.
  unfold not; intro; assumption.
  assert (L: 0 < S t) by omega.
  remember (last (combine (ch (sys oneBeh (S t)) s c p) (labelCh (S t) s c p))
             (dmy, 0)) as lt.
  assert (rew: lt = (fst lt, snd lt)).
  destruct lt.
  reflexivity.
  rewrite rew in *.
  pose proof (@inImpSent s c p (fst lt) (snd lt) 0 (S t) L use sth3) as use2.
  unfold mark in use2.
  simpl in use2.
  destruct use2 as [x [y stf]].
  destruct (trans oneBeh x).
  intuition.
  intuition.

  simpl in *.
  destruct s.
  destruct (decTree c c0).
  destruct (decTree p p0).
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.

  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [[u1 [u2 _]] _].
  rewrite u1 in *; rewrite u2 in *.
  pose proof (noCycle c_p p1); intuition.


  intuition.

  destruct stf as [[u1 [u2 _]] _].
  rewrite u1 in *; rewrite u2 in *.
  pose proof (noCycle c_p p1); intuition.


  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.


  intuition.


  simpl in *.
  destruct s.
  destruct stf as [[_ [_ [u2 _]]] _].
  assumption.
  destruct stf as [_ u1].
  pose proof (listNeq _ _ (eq_sym u1)); intuition.

  intuition.
Qed.

Theorem noEnqDeq: forall {s p c t m1 m2}, recv s p c t m1 -> mark s p c t m2 -> False.
Proof.
  intros s p c t m1 m2 recvm1 markm2.
  unfold recv in *. unfold mark in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.
  pose proof (enqC2P p1 n) as ty; rewrite ty in recvm1.
  destruct recvm1 as [_ [_ [u1 _]]]; destruct markm2 as [_ [_ [u2 _]]].
  rewrite u1 in u2; discriminate.
  intuition.
  intuition.
  assert (H: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- H in recvm1; rewrite e in recvm1.
  destruct recvm1 as [_ [_ [u1 _]]]; destruct markm2 as [_ [_ [u2 _]]].
  rewrite u1 in u2; discriminate.
  intuition.
  intuition.
  intuition.
Qed.

Section Local.
  Context {s: ChannelType}.
  Context {p c: Cache}.
  Context {t: Time}.
  Definition comb := combine (ch (sys oneBeh t) s p c) (labelCh t s p c).

  Theorem posGreaterFull: forall {n}, n < length (ch (sys oneBeh t) s p c) ->
                                      forall {i}, i < n -> snd (nth n comb (dmy, 0)) <
                                                           snd (nth i comb (dmy, 0)).
  Proof.
    intros n n_lt i i_lt.
    pose proof (@lenEq s p c t) as lEq.
    rewrite lEq in n_lt.
    pose proof (posGreater n_lt i_lt) as almost.
    pose proof (eqComb dmy 0 n lEq) as bestn.
    pose proof (eqComb dmy 0 i lEq) as besti.
    unfold snd.
    unfold comb.
    rewrite bestn; rewrite besti.
    assumption.
  Qed.

  Theorem posGreaterFull': forall {n}, n < length comb ->
                                       forall {i}, i < n -> snd (nth n comb (dmy, 0)) <
                                                            snd (nth i comb (dmy, 0)).
  Proof.
    pose proof (combLength (@lenEq s p c t)) as H.
    unfold comb.
    rewrite <- H.
    apply @posGreaterFull.
  Qed.

  Theorem posNeq: In (last (ch (sys oneBeh t) s p c) dmy, last (labelCh t s p c) 0)
                     (combine (removelast (ch (sys oneBeh t) s p c))
                              (removelast (labelCh t s p c))) -> False.
  Proof.
    intros isIn.
    pose proof (removeCombine (ch (sys oneBeh t) s p c) (labelCh t s p c)) as eq.
    rewrite <- eq in isIn; clear eq.
    pose proof (lastCombineDist (ch (sys oneBeh t) s p c) dmy (labelCh t s p c) 0 (@lenEq s p c t)) as use1.
    rewrite <- use1 in isIn.
    pose proof (lastInRemove isIn) as [i [cond1 cond2]].
    pose proof (last_nth comb (dmy, 0)) as cond3.
    pose proof (@lenEq s p c t) as H.
    pose proof (combLength H) as H0.
    fold comb in H0.
    rewrite <- H0 in cond3.
    assert (length (ch (sys oneBeh t) s p c) <> 0).
    unfold comb in *; rewrite <- H0 in cond1.
    unfold not; intro K.
    rewrite K in cond1.
    omega.
    assert (one: length (ch (sys oneBeh t) s p c) - 1 < length (ch (sys oneBeh t) s p c)) by
           omega.
    unfold comb in H0.
    rewrite <- H0 in cond1.
    pose proof (posGreaterFull one cond1).
    rewrite cond3 in H2.
    unfold comb in H2.
    rewrite cond2 in H2.
    omega.
  Qed.

  Theorem allLow: forall {b l}, In (b, l) comb -> (b, l) = last comb (dmy, 0) \/
                                                  l > snd (last comb (dmy, 0)).
  Proof.
    intros b l isIn.
    pose proof (last_nth comb (dmy, 0)) as whichNth.
    pose proof (@in_nth (BaseMesg * nat) comb (b, l) (dmy, 0) isIn) as [i [cond posi]].
    assert (i = length comb - 1 \/ i < length comb - 1) by omega.
    destruct H as [eq|neq].
    rewrite eq in posi.
    rewrite posi in whichNth.
    left; assumption.
    assert (K: length comb - 1 < length comb) by omega.
    pose proof (posGreaterFull' K neq) as use.
    rewrite whichNth in use.
    rewrite posi in use.
    simpl in use.
    right; assumption.
  Qed.

  Theorem allLowRecv: forall {b l m s'}, In (b, l) comb -> recv s' p c t m -> recvc t = s ->
                                      msgId m > l -> False.
  Proof.
    intros b l m s' isIn recvm which gt.
    unfold recvc in which.
    pose proof (allLow isIn) as useful.
    pose proof (lastCombineDist _ dmy _ 0 (@lenEq s p c t)) as dist.
    unfold comb in useful; rewrite dist in useful.
    assert (use': l = last (labelCh t s p c) 0 \/ l > last (labelCh t s p c) 0).
    destruct useful.
    left.
    injection H as u1 u2.
    assumption.
    simpl in H.
    right.
    assumption.
    rewrite <- which in use'.
    simpl in useful; clear dist useful.
    unfold recv in recvm.
    destruct (trans oneBeh t).
    intuition.
    intuition.
    intuition.
    destruct recvm as [u1 [u2 [u3 [_ [_ [_ [_ u]]]]]]].
    rewrite <- u1 in *; rewrite <- u2 in *; rewrite <- u in *; omega.
    destruct recvm as [u1 [u2 [u3 [_ [_ [_ [_ u]]]]]]].
    rewrite <- u1 in *; rewrite <- u2 in *; rewrite <- u in *; omega.
    intuition.
    destruct recvm as [u1 [u2 [u3 [_ [_ [_ [_ u]]]]]]].
    rewrite <- u1 in *; rewrite <- u2 in *; rewrite <- u in *; omega.
    destruct recvm as [u1 [u2 [u3 [_ [_ [_ [_ u]]]]]]].
    rewrite <- u1 in *; rewrite <- u2 in *; rewrite <- u in *; omega.
    intuition.
    destruct recvm as [u1 [u2 [u3 [_ [_ [_ [_ u]]]]]]].
    rewrite <- u1 in *; rewrite <- u2 in *; rewrite <- u in *; omega.
  Qed.
End Local.

Theorem useful: forall {s p c t1 t2 m1 m2},
                  recv s p c t1 m1 -> recv s p c t2 m2 -> recvc t1 = recvc t2.
  intros s p c t1 t2 m1 m2 recv1 recv2.
  unfold recv in *.
  unfold recvc in *.
  destruct (trans oneBeh t1); destruct (trans oneBeh t2); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  pose proof (noCycle p1 p3).
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  pose proof (enqC2P p1 n).
  pose proof (enqC2P p3 n0).
  rewrite <- H2 in *; rewrite H16 in *; rewrite H13 in *; discriminate.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
  pose proof (enqC2P p1 n).
  pose proof (enqC2P p3 n0).
  rewrite <- H2 in *; rewrite H16 in *; rewrite H13 in *; discriminate.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3;
  pose proof (noCycle p1 p3).
  intuition.
Qed.

Theorem recvNotIn: forall {s p c t m}, recv s p c t m ->
                                       In (Build_BaseMesg (from m) (to m) (addr m) (dataM m)
                                                          s, msgId m)
                                          (combine (ch (sys oneBeh (S t)) (recvc t) p c)
                                                   (labelCh (S t) (recvc t) p c)) -> False.
Proof.
  intros s p c t m recvm isIn.
  unfold recv in recvm. unfold recvc in isIn. unfold labelCh in isIn; fold labelCh in isIn.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e0 in *.
  destruct (decTree c p0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) rch p c) dmy, last (labelCh t rch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) rch p c)) (removelast (labelCh t rch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) rch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  intuition.
  intuition.
  destruct (decTree c p0); intuition.

  simpl in isIn.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  intuition.
  intuition.
  intuition.

  intuition.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e0 in *.
  destruct (decTree c p0).
  rewrite <- e1 in *.
  destruct recvm as [u1 [u2 _]].
  pose proof (noParentChild u2 p1).
  intuition.
  destruct (decTree c p).
  rewrite <- e1 in *.
  destruct (decTree p p0).
  rewrite <- e2 in *.
  intuition.
  destruct (decTree c p0).
  intuition.
  intuition.
  intuition.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  destruct (decTree c p).
  rewrite <- e2 in *.
  pose proof (noParentChild eq_refl p1).
  intuition.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  intuition.
  destruct (decTree c p).
  intuition.
  intuition.
  destruct (decTree c p0); destruct (decTree c c0); intuition.

  simpl in isIn.
  destruct (decTree p c0).
  rewrite <- e0 in *.
  destruct (decTree c p0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  intuition.
  intuition.
  intuition.


  intuition.

  simpl in *.
  destruct (decTree p p0).
  rewrite <- e0 in *.
  destruct (decTree c c0).
  rewrite <- e1 in *.
  assert (gd: In (last (ch (sys oneBeh t) mch p c) dmy, last (labelCh t mch p c) 0)
                 (combine (removelast (ch (sys oneBeh t) mch p c)) (removelast (labelCh t mch p c)))).
  destruct recvm as [_ [_ [u1 [u2 [u3 [u4 [ u5 u6]]]]]]].
  rewrite u1 in isIn; rewrite u2 in isIn; rewrite u3 in isIn; rewrite u4 in isIn;
  rewrite u5 in isIn; rewrite u6 in isIn;
  destruct (last (ch (sys oneBeh t) mch p c) dmy).
  simpl in *.
  assumption.
  pose proof (posNeq gd).
  intuition.
  intuition.
  intuition.
Qed.

Theorem recvLast: forall {s p c t m}, recv s p c t m ->
                                      last (combine (ch (sys oneBeh t) (recvc t) p c)
                                                    (labelCh t (recvc t) p c)) (dmy, 0) =
                                      (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s,
                                      msgId m).
Proof.
  intros s p c t m recvm.
  unfold recv in *.
  unfold recvc in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) rch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq rch c0 p0 t)) as r2.
  auto.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: m0 = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct m0.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: m0 = last (ch (sys oneBeh t) mch c0 p0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct m0.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch c0 p0 t)) as r2.
  auto.
  intuition.
  destruct recvm as [u1 [u2 [u3 [u4 [u5 [u6 [u7 u8]]]]]]].
  assert (rew: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
  rewrite <- rew in *.
  rewrite <- u1 in *; rewrite <- u2 in *. rewrite u3 in *; rewrite u4 in *; rewrite u5 in *;
  rewrite u6 in *; rewrite u7 in *; rewrite u8 in *.
  destruct r.
  simpl in *.
  rewrite rew.
  pose proof (lastCombineDist _ dmy _ 0 (@lenEq mch p0 c0 t)) as r2.
  auto.
Qed.

Theorem uniqRecv2': forall {s1 s2 p c t1 t2 m1 m2},
                     recv s1 p c t1 m1 -> recv s2 p c t2 m2 -> t1 < t2 -> recvc t1 = recvc t2 ->
                     msgId m1 < msgId m2.
Proof.
  intros s1 s2 p c t1 t2 m1 m2 recvm1 recvm2 t1_lt_t2 eq_recv.
  pose proof (recvImpIn recvm1) as H1.
  pose proof (recvImpIn recvm2) as H2.
  destruct (classic (In ({|
          fromB := from m2;
          toB := to m2;
          addrB := addr m2;
          dataBM := dataM m2;
          type := s2 |}, msgId m2) ( (combine (ch (sys oneBeh t1) (recvc t2) p c)
            (labelCh t1 (recvc t2) p c))))) as [pos|enq].
  rewrite <- eq_recv in pos.
  assert (mDec: {(Build_BaseMesg (from m1) (to m1) (addr m1) (dataM m1) s1, msgId m1) =
                (Build_BaseMesg (from m2) (to m2) (addr m2) (dataM m2) s2, msgId m2)} +
               {(Build_BaseMesg (from m1) (to m1) (addr m1) (dataM m1) s1, msgId m1) <>
                (Build_BaseMesg (from m2) (to m2) (addr m2) (dataM m2) s2, msgId m2)}).
  repeat decide equality.
  apply decData.
  apply decAddr.
  destruct mDec as [same|diff].
  rewrite <- same in *.
  pose proof (recvNotIn recvm1) as notIn.
  assert (S t1 = t2 \/ S t1 < t2) by omega.
  destruct H as [easy | hard].
  rewrite easy in *.
  rewrite eq_recv in *.
  intuition.
  rewrite eq_recv in *.
  pose proof (inImpSent hard H2 notIn) as [t2i [cond2 [mark2 rest2]]].
  simpl in mark2.
  pose proof (msgIdTime mark2) as gt.
  simpl in gt.
  pose proof (inImpSent2 H1) as [t1i [cond1 [mark1 rest1]]].
  simpl in mark1.
  pose proof (msgIdTime mark1) as lt.
  simpl in lt.
  omega.

  pose proof (last_nth (combine (ch (sys oneBeh t1) (recvc t1) p c) (labelCh t1 (recvc t1) p c)) (dmy, 0)) as isLast.
  pose proof (in_nth (dmy, 0) pos) as [i [i_lt eq]].

  assert (i = length (combine (ch (sys oneBeh t1) (recvc t1) p c)
                              (labelCh t1 (recvc t1) p c)) - 1 \/
         i < length (combine (ch (sys oneBeh t1) (recvc t1) p c)
                    (labelCh t1 (recvc t1) p c)) - 1) by omega.
  destruct H as [isEq | neq].
  rewrite isEq in eq.
  rewrite isLast in eq.

  pose proof (recvLast recvm1) as H.
  rewrite H in eq.
  intuition.


  pose proof (combLength (@lenEq (recvc t1) p c t1)) as H0.
  rewrite <- H0 in neq.
  rewrite <- H0 in i_lt.

  assert (la: length (ch (sys oneBeh t1) (recvc t1) p c) - 1 < length (ch (sys oneBeh t1)
                                                                      (recvc t1) p c))
    by omega.
  pose proof (posGreaterFull la neq) as almost.
  rewrite <- H0 in isLast.
  unfold comb in almost.
  rewrite isLast in almost.
  rewrite eq in almost.
  pose proof (recvLast recvm1) as K.
  rewrite K in almost.
  simpl in almost.
  assumption.


  pose proof (inImpSent t1_lt_t2 H2 enq) as [t2i [cond2 [mark2 rest2]]].
  simpl in mark2.
  pose proof (inImpSent2 H1) as [t1i [cond1 [mark1 rest1]]].
  simpl in mark1.

  pose proof (msgIdTime mark1) as lt.
  pose proof (msgIdTime mark2) as gt.
  simpl in *.
  rewrite lt; rewrite gt; omega.
Qed.

Theorem uniqRecv2: forall {s p c t1 t2 m},
                     recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
Proof.
  intros s p c t1 t2 m recv1 recv2.
  pose proof (useful recv1 recv2).
  unfold Time in *.
  assert (t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
  destruct H0 as [eq | [lt | gt]].
  assumption.
  pose proof (uniqRecv2' recv1 recv2 lt H).
  omega.
  assert (recvc t2 = recvc t1) by auto.
  pose proof (uniqRecv2' recv2 recv1 gt H0).
  omega.
Qed.

Theorem uniqMark1: forall {s p c m n t}, mark s p c t m -> mark s p c t n -> m = n.
Proof.
  intros s p c m n t markm markn.
  unfold mark in *.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
  destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
  rewrite <- fromm in fromn;
    rewrite <- tom in ton;
    rewrite <- addrm in addrn;
    rewrite <- datam in datan;
    rewrite <- idm in idn.
  destruct m; destruct n; simpl in *.
  rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
  reflexivity.

  destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
  destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
  rewrite <- fromm in fromn;
    rewrite <- tom in ton;
    rewrite <- addrm in addrn;
    rewrite <- datam in datan;
    rewrite <- idm in idn.
  destruct m; destruct n; simpl in *.
  rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
  reflexivity.

  intuition.

  destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
  destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
  rewrite <- fromm in fromn;
    rewrite <- tom in ton;
    rewrite <- addrm in addrn;
    rewrite <- datam in datan;
    rewrite <- idm in idn.
  destruct m; destruct n; simpl in *.
  rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
  reflexivity.

  destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
  destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
  rewrite <- fromm in fromn;
    rewrite <- tom in ton;
    rewrite <- addrm in addrn;
    rewrite <- datam in datan;
    rewrite <- idm in idn.
  destruct m; destruct n; simpl in *.
  rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
  reflexivity.

  intuition.

  destruct markm as [_ [_ [_ [fromm [tom [addrm [datam idm]]]]]]].
  destruct markn as [_ [_ [_ [fromn [ton [addrn [datan idn]]]]]]].
  rewrite <- fromm in fromn;
    rewrite <- tom in ton;
    rewrite <- addrm in addrn;
    rewrite <- datam in datan;
    rewrite <- idm in idn.
  destruct m; destruct n; simpl in *.
  rewrite fromn; rewrite ton; rewrite addrn; rewrite datan; rewrite idn.
  reflexivity.

  intuition.
Qed.

Theorem uniqMark2: forall {s p c m t1 t2}, mark s p c t1 m -> mark s p c t2 m -> t1 = t2.
Proof.
  intros s p c m t1 t2 markm1 markm2.
  unfold mark in *.

  destruct (trans oneBeh t1).
  intuition.
  intuition.

  destruct (trans oneBeh t2).
  intuition.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.

  intuition.

  destruct (trans oneBeh t2).
  intuition.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.

  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.

  intuition.

  destruct (trans oneBeh t2).
  intuition.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.

  destruct (trans oneBeh t2).
  intuition.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.

  intuition.

  destruct (trans oneBeh t2).
  intuition.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.
  destruct markm1 as [_ [_ [_ [_ [_ [_ [_ u1]]]]]]];
    destruct markm2 as [_ [_ [_ [_ [_ [_ [_ u2]]]]]]];
    rewrite u1 in u2; assumption.
  intuition.

  intuition.
Qed.

Theorem toCSameCh: forall {x1 x2 p c t1 t2 m r}, parent c p ->
                                                 mark x1 p c t1 m ->
                                                 recv x2 p c t2 r ->
                                                 recvc t2 = markc t1.
Proof.
  intros x1 x2 p c t1 t2 m r c_p mark1 recv2.
  unfold mark in *; unfold recv in *.
  unfold markc; unfold recvc.
  destruct (trans oneBeh t1); destruct (trans oneBeh t2); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p1); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p1); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p3); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p1); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p3); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p3); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p3); intuition.
  rewrite H in p1; rewrite H1 in p3; rewrite H3 in p1; rewrite H0 in p3.
  pose proof (noCycle c_p p3); intuition.
Qed.  


Theorem fifo1: forall {p c t1 t2 t3 m r}, parent c p ->
                 mark mch p c t1 m ->
                 mark rch p c t2 r -> recv rch p c t3 r -> t1 <= t2 ->
                 exists t4, t4 < t3 /\ recv mch p c t4 m.
Proof.
  intros p c t1 t2 t3 m r c_p markm markr recvr t1_le_t2.
  unfold Time in *. unfold labelCh in *; fold labelCh in *.
  assert (t1 = t2 \/ t1 < t2) by omega; clear t1_le_t2.
  destruct H as [eq | t1_lt_t2].
  rewrite eq in *.
  pose proof (noEnqMR markm markr); intuition.
  pose proof (enqImpIn markm) as inm.
  pose proof (recvImpSend' recvr) as [tx [tx_le_t3 mark'r]].
  unfold send in mark'r.
  pose proof (uniqMark2 markr mark'r) as H.
  rewrite <- H in *; clear mark'r H.
  assert (S t1 = t3 \/ S t1 < t3) by omega.
  destruct H as [ez|hard].
  omega.
  destruct (classic (In ({|
           fromB := from m;
           toB := to m;
           addrB := addr m;
           dataBM := dataM m;
           type := mch |}, msgId m) (combine (ch (sys oneBeh t3) (markc t1) p c)
             (labelCh t3 (markc t1) p c)))) as [pres|noPres].
  pose proof (msgIdTime markm) as sth1.
  pose proof (msgIdTime markr) as sth2.
  rewrite <- sth1 in t1_lt_t2.
  rewrite <- sth2 in t1_lt_t2.
  pose proof (toCSameCh c_p markm recvr) as markEq.
  pose proof (allLowRecv pres recvr markEq) as contra.
  intuition.
  pose proof (notInImpExRecv hard noPres inm) as mustRecv.
  simpl in mustRecv.
  destruct mustRecv as [t [cond [recvt _]]].
  exists t.
  intuition.
Qed.


Theorem fifo2: forall {p c t1 t2 t3 m r}, parent c p ->
                 mark rch p c t1 m ->
                 mark mch p c t2 r -> recv mch p c t3 r -> t1 <= t2 ->
                 exists t4, t4 < t3 /\ recv rch p c t4 m.
Proof.
  intros p c t1 t2 t3 m r c_p markm markr recvr t1_le_t2.
  unfold Time in *. unfold labelCh in *; fold labelCh in *.
  assert (t1 = t2 \/ t1 < t2) by omega; clear t1_le_t2.
  destruct H as [eq | t1_lt_t2].
  rewrite eq in *.
  pose proof (noEnqMR markr markm); intuition.
  pose proof (enqImpIn markm) as inm.
  pose proof (recvImpSend' recvr) as [tx [tx_le_t3 mark'r]].
  unfold send in mark'r.
  pose proof (uniqMark2 markr mark'r) as H.
  rewrite <- H in *; clear mark'r H.
  assert (S t1 = t3 \/ S t1 < t3) by omega.
  destruct H as [ez|hard].
  omega.
  destruct (classic (In ({|
           fromB := from m;
           toB := to m;
           addrB := addr m;
           dataBM := dataM m;
           type := rch |}, msgId m) (combine (ch (sys oneBeh t3) (markc t1) p c)
             (labelCh t3 (markc t1) p c)))) as [pres|noPres].
  pose proof (msgIdTime markm) as sth1.
  pose proof (msgIdTime markr) as sth2.
  rewrite <- sth1 in t1_lt_t2.
  rewrite <- sth2 in t1_lt_t2.
  pose proof (toCSameCh c_p markm recvr) as markEq.
  pose proof (allLowRecv pres recvr markEq) as contra.
  intuition.
  pose proof (notInImpExRecv hard noPres inm) as mustRecv.
  simpl in mustRecv.
  destruct mustRecv as [t [cond [recvt _]]].
  exists t.
  intuition.
Qed.

Theorem c2pRecvSame: forall {s p c t m},
                       parent c p ->
                       recv s c p t m ->
                       s = recvc t.
Proof.
  intros s p c t m c_p recvm.
  unfold recv in *; unfold recvc.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  intuition.

  pose proof (enqC2P p1 n).
  rewrite H in recvm.
  intuition.

  unfold m0 in e.
  rewrite e in recvm.
  intuition.

  intuition.

  destruct recvm as [u1 [u2 _]].
  rewrite <- u1 in *; rewrite <- u2 in *.
  pose proof (noCycle c_p p1); intuition.

  pose proof (enqC2P p1 n).
  rewrite H in recvm.
  intuition.

  intuition.

  destruct recvm as [u1 [u2 _]].
  rewrite <- u1 in *; rewrite <- u2 in *.
  pose proof (noCycle c_p p1); intuition.
Qed.


Theorem c2pMarkSame: forall {s p c t m},
                       parent c p ->
                       mark s c p t m ->
                       s = markc t.
Proof.
  intros s p c t m c_p recvm.
  unfold mark in *; unfold markc.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  intuition.

  intuition.

  intuition.

  destruct recvm as [u1 [u2 _]].
  rewrite <- u1 in *; rewrite <- u2 in *.
  pose proof (noCycle c_p p1); intuition.

  intuition.

  intuition.

  intuition.

  intuition.
Qed.

Theorem p2cMarkMch: forall {s p c t m},
                       parent c p ->
                       mark s p c t m ->
                       mch = markc t.
Proof.
  intros s p c t m c_p recvm.
  unfold mark in *; unfold markc.
  destruct (trans oneBeh t).
  intuition.
  intuition.

  destruct recvm as [u1 [u2 _]].
  rewrite <- u1 in *; rewrite <- u2 in *.
  pose proof (noCycle c_p p1); intuition.

  intuition.

  intuition.

  intuition.

  intuition.

  intuition.

  intuition.

  intuition.
Qed.

Theorem p2cRecvMch: forall {s p c t m},
                       parent c p ->
                       recv s p c t m ->
                       mch = recvc t.
Proof.
  intros s p c t m c_p recvm.
  unfold recv in *; unfold recvc.
  destruct (trans oneBeh t); intuition.
  rewrite <- H in *; rewrite <- H1 in *.
  pose proof (noCycle c_p p1); intuition.
Qed.

Theorem cRecvImpNotIn: forall {s p c t rm m},
                         rm < t ->
                         parent c p ->
                         recv s c p rm m ->
                         ~ In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s, msgId m)
                           (combine (ch (sys oneBeh t) s c p) (labelCh t s c p)).
Proof.
  unfold not; intros s p c t rm m rm_lt_t c_p recvm isIn.
  pose proof (recvNotIn recvm) as sth.
  pose proof (c2pRecvSame c_p recvm) as H.
  rewrite <- H in sth.
  assert (t = S rm \/ S rm < t) by omega.
  destruct H0.
  rewrite <- H0 in *.
  intuition.
  pose proof (inImpSent H0 isIn sth) as [ti [cond [H2 _]]].
  simpl in *.
  pose proof (recvImpSend' recvm) as [ti' [cond' H2']].
  assert (m = (Build_Mesg (from m) (to m) (addr m) (dataM m) (msgId m))).
  destruct m.
  reflexivity.
  rewrite <- H1 in H2.
  pose proof (uniqMark2 H2' H2).
  omega.
Qed.

Theorem pRecvImpNotIn: forall {s p c t rm m},
                         rm < t ->
                         parent c p ->
                         recv s p c rm m ->
                         ~ In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s, msgId m)
                           (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)).
Proof.
  unfold not; intros s p c t rm m rm_lt_t c_p recvm isIn.
  pose proof (recvNotIn recvm) as sth.
  pose proof (p2cRecvMch c_p recvm) as H.
  rewrite <- H in sth.
  assert (t = S rm \/ S rm < t) by omega.
  destruct H0.
  rewrite <- H0 in *.
  intuition.
  pose proof (inImpSent H0 isIn sth) as [ti [cond [H2 _]]].
  simpl in *.
  pose proof (recvImpSend' recvm) as [ti' [cond' H2']].
  assert (m = (Build_Mesg (from m) (to m) (addr m) (dataM m) (msgId m))).
  destruct m.
  reflexivity.
  rewrite <- H1 in H2.
  pose proof (uniqMark2 H2' H2).
  omega.
Qed.

Theorem cSendNotRecvImpIn:
  forall {s p c t sm m},
    sm < t ->
    parent c p ->
    send s c p sm m ->
    (forall y, sm < y < t -> ~ recv s c p y m) ->
    In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s, msgId m)
      (combine (ch (sys oneBeh t) s c p) (labelCh t s c p)).
Proof.
  intros s p c t sm m sm_lt_t c_p sendm norecvm.
  destruct (classic (In
     ({|
      fromB := from m;
      toB := to m;
      addrB := addr m;
      dataBM := dataM m;
      type := s |}, msgId m)
     (combine (ch (sys oneBeh t) s c p) (labelCh t s c p)))).
  assumption.
  simpl in *.
  pose proof (enqImpIn sendm).
  pose proof (c2pMarkSame c_p sendm).
  rewrite <- H1 in H0.
  assert (S sm = t \/ S sm < t) by omega.
  destruct H2.
  rewrite H2 in *.
  intuition.
  pose proof (notInImpExRecv H2 H H0) as [rt [condrt [stf _]]].
  simpl in stf.
  assert (m = Build_Mesg (from m) (to m) (addr m) (dataM m) (msgId m)) by
      (destruct m; reflexivity).
  rewrite <- H3 in stf.
  specialize (norecvm rt condrt stf).
  intuition.
Qed.


Theorem pSendNotRecvImpIn:
  forall {s p c t sm m},
    sm < t ->
    parent c p ->
    send s p c sm m ->
    (forall y, sm < y < t -> ~ recv s p c y m) ->
    In (Build_BaseMesg (from m) (to m) (addr m) (dataM m) s, msgId m)
      (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)).
Proof.
  intros s p c t sm m sm_lt_t c_p sendm norecvm.
  destruct (classic (In
     ({|
      fromB := from m;
      toB := to m;
      addrB := addr m;
      dataBM := dataM m;
      type := s |}, msgId m)
     (combine (ch (sys oneBeh t) mch p c) (labelCh t mch p c)))).
  assumption.
  simpl in *.
  pose proof (enqImpIn sendm).
  pose proof (p2cMarkMch c_p sendm).
  rewrite <- H1 in H0.
  assert (S sm = t \/ S sm < t) by omega.
  destruct H2.
  rewrite H2 in *.
  intuition.
  pose proof (notInImpExRecv H2 H H0) as [rt [condrt [stf _]]].
  simpl in stf.
  assert (m = Build_Mesg (from m) (to m) (addr m) (dataM m) (msgId m)) by
      (destruct m; reflexivity).
  rewrite <- H3 in stf.
  specialize (norecvm rt condrt stf).
  intuition.
Qed.

