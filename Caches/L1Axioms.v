Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams DataTypes.

Opaque oneBeh.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqOrNot: forall t, {x| deqR (fst (fst x)) (snd (fst x)) (snd x) t} + {forall a c i, ~ deqR a c i t}.
  Proof.
    intros t.
    unfold deqR.
    destruct (trans oneBeh t).
    (left; apply (exist _ (a, c, (req (sys oneBeh t) a c)))); intuition.
    (left; apply (exist _ (a, c, (req (sys oneBeh t) a c)))); intuition.
    right; intuition.
    right; intuition.
    right; intuition.
    right; intuition.
    right; intuition.
    right; intuition.
    right; intuition.
    right; intuition.
  Qed.

  Theorem deqLeaf: forall {c a i t}, deqR a c i t -> leaf c.
  Proof.
    intros c a i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
      (simpl in *; destruct (decTree c c0) as [eq|notEq];
       [rewrite eq in *; intuition| intuition]);
      assert (c = c0) by auto; intuition.
  Qed.

  Theorem deqDef: forall {c a i t}, deqR a c i t -> defined c.
  Proof.
    intros c a i t deqr.
    unfold deqR in deqr.
    destruct (trans oneBeh t);
    (simpl in *; destruct (decTree c c0) as [eq|notEq]; [rewrite eq in *; firstorder| firstorder]);
    assert (c = c0) by auto; firstorder.
  Qed.

  Theorem uniqDeqProc: forall {c a i1 t i2},
                       deqR a c i1 t -> deqR a c i2 t ->
                       i1 = i2.
  Proof.
    intros c a i1 t i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t); intuition.
  Qed.

  Theorem processDeq: forall {c a i t}, deqR a c i t ->
                                      let q := reqFn a c i in
                                      match desc q with
                                        | Ld => sle Sh (state c a t)
                                        | St => state c a t = Mo
                                      end.
  Proof.
    intros c a i t deqr.
    unfold state.
    unfold deqR in *.
    destruct (trans oneBeh t).

    destruct deqr as [e1 [eq u1]].
    rewrite e1 in *.
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    destruct deqr as [e1 [eq u1]].
    rewrite e1 in *.
    rewrite eq in *.
    rewrite u1 in *.
    rewrite e in *.
    assumption.

    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.



  Theorem reqGe: forall {c a t1 t2}, t1 <= t2 -> req (sys oneBeh t2) a c >= req (sys oneBeh t1) a c.
  Proof.
    intros c a t1 t2 le.
    remember (t2 - t1) as td.
    assert (t2 = t1 + td) by omega.
    rewrite H in *; clear le Heqtd H.
    induction td.
    assert (t1 + 0 = t1) by omega.
    rewrite H.
    omega.
    assert (t1 + S td = S (t1 + td)) by omega.
    rewrite H; clear H.
    assert (req (sys oneBeh (S (t1 + td))) a c >= req (sys oneBeh (t1 + td)) a c).
    destruct (trans oneBeh (t1 + td)).

    simpl.
    destruct (decAddr a a0); destruct (decTree c c0); omega.
    simpl.
    destruct (decAddr a a0); destruct (decTree c c0); omega.
    simpl.
    omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
    simpl; omega.
  Qed.

  Theorem reqGeConv: forall {c a t1 t2}, req (sys oneBeh t1) a c < req (sys oneBeh t2) a c -> t1 < t2.
  Proof.
    intros c a t1 t2 reqEq.
    assert (t1 >= t2 \/ t1 < t2) by omega.
    destruct H.
    pose proof (@reqGe c a _ _ H) as contra; omega.
    assumption.
  Qed.

  Theorem reqGt: forall {c a i t1 t2}, t1 < t2 -> deqR a c i t1 ->
                                     req (sys oneBeh t2) a c > i.
  Proof.
    intros c a i t1 t2 cond deqr.
    assert (S t1 <= t2) by omega.
    assert (req (sys oneBeh (S t1)) a c > i).
    unfold deqR in *.
    destruct (trans oneBeh t1).
    simpl.
    destruct deqr as [eq1 [eq sth]].
    rewrite eq1, eq in *.
    destruct (decAddr a a); destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    firstorder.
    firstorder.
    simpl.
    destruct deqr as [eq1 [eq sth]].
    rewrite eq1, eq in *.
    destruct (decAddr a a); destruct (decTree c c).
    rewrite sth; omega.
    firstorder.
    firstorder.
    firstorder.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (@reqGe c a _ _ H).
    omega.
  Qed.

  Theorem uniqDeqProc2: forall {c a i t1 t2},
                        deqR a c i t1 -> deqR a c i t2 -> t1 = t2.
  Proof.
    intros c a i t1 t2 deq1 deq2.
    unfold Time in *.
    assert (t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct H as [e1 | [e2 | e3]].
    assumption.
    pose proof (reqGt e2 deq1).
    unfold deqR in deq2.
    destruct (trans oneBeh t2).
    destruct deq2 as [_ u2].
    omega.
    destruct deq2 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    pose proof (reqGt e3 deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u2].
    omega.
    destruct deq1 as [_ u2].
    omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem uniqDeqProc3: forall {c1 a1 i1 t c2 a2 i2},
                          deqR a1 c1 i1 t -> deqR a2 c2 i2 t ->
                          a1 = a2 /\ c1 = c2 /\ i1 = i2.
  Proof.
    intros c1 a1 i1 t c2 a2 i2 deq1 deq2.
    unfold deqR in *.
    destruct (trans oneBeh t).
    destruct deq2 as [x [y z]].
    destruct deq1 as [x1 [y1 z1]].
    rewrite <- x, <- y, <- x1, <- y1 in *.
    intuition.
    destruct deq2 as [x [y z]].
    destruct deq1 as [x1 [y1 z1]].
    rewrite <- x, <- y, <- x1, <- y1 in *.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem incReqImpDeq: forall {c a t i},
                           req (sys oneBeh t) a c > i ->
                           exists t', t' < t /\ deqR a c i t'.
  Proof.
    intros c a t i reqEq.
    induction t.
    pose proof (init oneBeh) as sth.
    rewrite sth in reqEq; clear sth.
    unfold initGlobalState in *; simpl in *.
    omega.
    assert (inc:req (sys oneBeh (S t)) a c = req (sys oneBeh t) a c \/
                req (sys oneBeh (S t)) a c = S (req (sys oneBeh t) a c)).
    destruct (trans oneBeh t).
    simpl in *.
    destruct (decAddr a a0); destruct (decTree c c0).
    right.
    intuition.
    intuition.
    intuition.
    intuition.
    simpl in *.
    destruct (decAddr a a0); destruct (decTree c c0).
    right.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.
    simpl in *; left; intuition.

    destruct inc.
    rewrite H in reqEq.
    specialize (IHt reqEq).
    destruct IHt as [t' [t'_lt_t deq]].
    exists t'.
    assert (t' < S t) by omega; intuition.
    rewrite H in reqEq.
    assert (opts: req (sys oneBeh t) a c > i \/ req (sys oneBeh t) a c = i) by omega.
    destruct H.
    destruct opts.
    specialize (IHt H).
    destruct IHt as [t' [t'_lt_t deq]].
    exists t'.
    constructor.
    omega.
    assumption.

    rewrite <- H in *; clear H.
    exists t.
    constructor.
    omega.

    unfold deqR.
    destruct (trans oneBeh t).
    simpl in *.
    destruct (decAddr a a0); destruct (decTree c c0).
    constructor; auto.
    omega.
    omega.
    omega.
    simpl in *.
    destruct (decAddr a a0); destruct (decTree c c0).
    constructor; auto.
    omega.
    omega.
    omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
    simpl in *; omega.
  Qed.

  Theorem deqImpDeqBefore: forall {c a i1 i2 t},
                             deqR a c i1 t -> i2 < i1 -> exists t', t' < t /\ deqR a c i2 t'.
  Proof.
    intros c a i1 i2 t deq i2_lt_i1.
    unfold deqR in deq.
    destruct (trans oneBeh t).
    destruct deq as [e1 [eq sth]].
    rewrite e1, eq in *.
    rewrite <- sth in *.
    pose proof (incReqImpDeq i2_lt_i1) as [x [z y]]; exists x; intuition.
    destruct deq as [e1 [eq sth]].
    rewrite e1,eq in *.
    rewrite <- sth in *.
    pose proof (incReqImpDeq i2_lt_i1) as [x [z y]]; exists x; intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem deqOrder: forall {c a i1 t1 i2 t2},
                      deqR a c i1 t1 -> deqR a c i2 t2 ->
                      i1 < i2 -> ~ t1 > t2.
  Proof.
    unfold not; intros c a i1 t1 i2 t2 deq1 deq2 iLess t2Less.
    pose proof (reqGt t2Less deq2).
    unfold deqR in deq1.
    destruct (trans oneBeh t1).
    destruct deq1 as [_ u]; omega.
    destruct deq1 as [_ u]; omega.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.
End mkL1Axioms.