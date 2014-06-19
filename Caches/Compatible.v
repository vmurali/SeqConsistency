Require Import DataTypes Channel Cache Coq.Logic.Classical Hier Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties MsiState.

Module Type CompatBehavior (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.
    Axiom sendPCond: forall {p}, defined n -> defined p -> parent n p ->
                                 forall {m},
                                   mark mch n p a t m ->
                                   forall {c}, defined c -> parent c n ->
                                               sle (dir n c a t) (to m).
    Axiom sendCCond: forall {c}, defined n -> defined c ->
                       parent c n ->
                       forall {m},
                         mark mch n c a t m ->
                         sle (to m) (state n a t) /\
                         forall {c'}, defined c' -> 
                                      c' <> c -> parent c' n -> sle (dir n c' a t)
                                      match to m with
                                        | Mo => In
                                        | Sh => Sh
                                        | In => Mo
                                      end.
    Axiom oneRespC: forall {c1 c2}, defined n -> defined c1 -> defined c2 ->
                      parent c1 n -> parent c2 n ->
                      forall {m1}, (mark mch n c1 a t m1 \/ recv mch c1 n a t m1) ->
                                   forall {m2},
                                     (mark mch n c2 a t m2 \/ recv mch c2 n a t m2) -> c1 = c2.
    Axiom respPNoRespC: forall {p}, defined n -> defined p -> parent n p ->
                                    forall {m},
                                      (mark mch n p a t m \/ recv mch p n a t m) ->
                                      forall {c}, defined c -> parent c n -> forall mc,
                                        ~ (mark mch n c a t mc \/ recv mch c n a t mc).
  End Node.
  Axiom initCompat:
    forall {n c}, defined n -> defined c -> parent c n -> forall a, dir n c a 0 = In.
End CompatBehavior.

Module Type CompatTheorem (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.
  Parameter compatible:
    forall {n}, defined n -> forall a t {c}, defined c -> parent c n ->
                        sle (dir n c a t) (state n a t) /\
                        forall {c'}, defined c' -> c' <> c -> parent c' n -> sle (dir n c' a t)
                                                                   match dir n c a t with
                                                                     | Mo => In
                                                                     | Sh => Sh
                                                                     | In => Mo
                                                                   end.
  Parameter compat:
    forall {n}, defined n -> forall a t {c}, defined c -> parent c n ->
                        sle (state c a t) (state n a t) /\
                        forall {c'}, defined c' -> c' <> c -> parent c' n -> sle (state c' a t)
                                                                   match state c a t with
                                                                     | Mo => In
                                                                     | Sh => Sh
                                                                     | In => Mo
                                                                   end.
  Parameter descSle: forall {c p}, defined c ->
                                   defined p -> descendent c p ->
                                   forall {a t},
                                     sle (state c a t) (state p a t).

  Parameter nonDescCompat: forall {c1 c2},
                           defined c1 -> defined c2 ->
                           ~ descendent c1 c2 -> ~ descendent c2 c1 ->
                           forall {a t},
                             sle (state c2 a t)
                                 match state c1 a t with
                                   | Mo => In
                                   | Sh => Sh
                                   | In => Mo
                                 end.

  Parameter allDirLower: forall {p}, defined p ->
                                     forall {co a t s},
                                       (forall c, defined c -> parent c p
                                                  -> sle (dir p c a t) s) ->
                                       co <> p -> descendent co p -> sle (state co a t) s.
End CompatTheorem.

Module mkCompat (dt: DataTypes) (ch: ChannelPerAddr dt) (cb: CompatBehavior dt ch) (ba: BehaviorAxioms dt ch)
                : CompatTheorem dt ch.
  Module mbt := mkBehaviorTheorems dt ch ba.
  Module hr := mkHierProperties dt.
  Import dt ch cb ba mbt hr.

  Theorem compatible:
    forall {n}, defined n -> forall a t {c}, defined c -> parent c n ->
                        sle (dir n c a t) (state n a t) /\
                        forall {c'}, defined c' -> c' <> c -> parent c' n -> sle (dir n c' a t)
                                                                   match dir n c a t with
                                                                     | Mo => In
                                                                     | Sh => Sh
                                                                     | In => Mo
                                                                   end.
  Proof.
    intros n nDef a t.
    induction t.
    intros c cDef cond.
    constructor.
    pose proof @initCompat n c nDef cDef cond a as c2.
    rewrite c2.
    unfold sle; destruct (state n a 0); auto.
    intros c' c'Def c'_ne_c c'Child.
    pose proof @initCompat n c' nDef c'Def c'Child a as c2.
    rewrite c2; destruct (dir n c a 0); unfold sle; auto.
    destruct (classic (exists p m, defined p /\
                           parent n p /\
                           (mark mch n p a t m \/ recv mch p n a t m))) as [respP|noRespP].
    destruct respP as [p [m [pDef [p_parent markOrRecv]]]].
    pose proof @respPNoRespC n a t p nDef pDef p_parent m markOrRecv as noChild.
    assert (sameDir: forall c, defined c -> parent c n -> dir n c a t = dir n c a (S t)).
    intros c cDef c_child.
    pose proof respPNoRespC nDef pDef p_parent markOrRecv cDef c_child as noRespC.
    assert (st_eq: dir n c a t = dir n c a (S t)).
    assert (stuff: {dir n c a t = dir n c a (S t)} + {dir n c a t <> dir n c a (S t)})
      by decide equality.
    destruct stuff as [eq|neq].
    assumption.
    assert (neq': dir n c a (S t) <> dir n c a t) by auto.
    pose proof (change (@dt n c nDef cDef c_child) neq') as resp.
    generalize noRespC resp; clear; firstorder.
    assumption.
    intros c cDef c_child.
    pose proof (sameDir c cDef c_child) as dir_eq.
    rewrite <- dir_eq in *.
    assert (sameC': forall c', defined c' -> c' <> c -> parent c' n -> dir n c' a t = dir n c' a (S t))
           by (generalize sameDir; clear; firstorder).
    destruct markOrRecv as [markm | recvm].
    pose proof (sendPCond nDef pDef p_parent markm cDef c_child) as dir_le_to_m.
    pose proof (sendmChange (@st p n pDef nDef p_parent) markm) as sth.
    constructor.

    rewrite <- sth in dir_le_to_m.
    assumption.

    intros c' c'Def. intros.
    specialize (sameC' c' c'Def H H0).
    rewrite <- sameC'.
    generalize IHt c cDef c_child c'Def H H0; clear; firstorder.
    constructor.
    pose proof (cRecvUpgrade pDef nDef p_parent recvm) as st_lt.
    generalize (IHt c cDef c_child) st_lt; clear; intros.
    destruct H as [stuff _].
    unfold sle in *; unfold sle in *; destruct (dir n c a t); destruct (state n a t);
    destruct (state n a (S t)); auto.
    intros c' c'Def c'Ne c'_child.
    specialize (sameDir c' c'Def c'_child).
    rewrite <- sameDir.
    generalize IHt c'_child c'Def c'Ne cDef c_child; clear; firstorder.
    assert (noRespP': forall p, defined p -> parent n p -> ~ ((exists m, mark mch n p a t m)
                                                   \/ (exists m, recv mch p n a t m)))
      by (
          generalize noRespP; clear; firstorder).
    assert (st_eq: state n a (S t) = state n a t).
    destruct (classic (exists p, defined p /\ parent n p)) as [[p [pDef p_parent]] | nop].
    specialize (noRespP' p pDef p_parent).
    assert (eqOrNot: {state n a (S t) = state n a t} + {state n a (S t) <> state n a t}) by
        decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    pose proof (noRespP' (change (@st p n pDef nDef p_parent) not)) as done.
    firstorder.
    assert (noP: forall p, defined p -> ~ parent n p) by firstorder.
    apply (@noParentSame n a t nDef noP).
    rewrite st_eq in *.

    destruct (classic (exists c m, defined c /\ parent c n /\ (mark mch n c a t m \/ recv mch c n a t m))) as [ex|notEx].
    destruct ex as [c [m [cDef [c_child resp]]]].
    assert (noneElse: forall c', defined c' -> c' <> c -> parent c' n ->
                       ~ ((exists m, mark mch n c' a t m) \/ exists m, recv mch c' n a t m)).
    intros c' c'Def c'_ne_c c'_child.
    destruct (classic (exists m', mark mch n c' a t m' \/ recv mch c' n a t m'))
      as [ex|notEx].
    destruct ex as [m' sth].
    pose proof (oneRespC nDef cDef c'Def c_child c'_child resp sth) as sth2.
    assert (c' = c) by auto.
    firstorder.
    firstorder.
    assert (stEq: forall c', defined c' -> c' <> c -> parent c' n -> dir n c' a (S t) = dir n c' a t).
    intros c' c'Def c'_ne_c c'_child.
    specialize (noneElse c' c'Def c'_ne_c c'_child).
    assert (eqOrNot: {dir n c' a (S t) = dir n c' a t} 
                     + {dir n c' a (S t) <> dir n c' a t}) by decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    specialize (noneElse (change (@dt n c' nDef c'Def c'_child) not)).
    firstorder.
    intros c0 c0Def c0_child.
    destruct (classic (c0 = c)) as [c0_eq_c|c0_ne_c].
    rewrite c0_eq_c in *.
    destruct resp as [markm | recvm].
    pose proof (sendmChange (@dt n c nDef cDef c_child) markm) as toM.
    rewrite toM.
    pose proof (sendCCond nDef cDef c_child markm) as [stuff rest].
    constructor.
    intuition.
    intros c' c'Def. intros.
    specialize (stEq c' c'Def H H0).
    rewrite stEq.
    specialize (rest c' c'Def H H0).
    intuition.
    pose proof (pRecvDowngrade nDef cDef c_child recvm) as sth_gt.
    constructor.
    destruct (IHt c cDef c_child) as [good bad].
    unfold slt in *; unfold sle in *; destruct (dir n c a (S t)); destruct (dir n c a t);
    destruct (state n a t); auto.
    clear c0 c0_child c0_eq_c.
    intros c' c'Def c'_ne_c c'_child.
    specialize (stEq c' c'Def c'_ne_c c'_child).
    rewrite stEq in *; clear stEq.
    destruct (IHt c cDef c_child) as [_ rest]; clear IHt.
    specialize (rest c' c'Def c'_ne_c c'_child).
    unfold slt in *; unfold sle in *; destruct (dir n c a (S t)); destruct (dir n c a t);
    destruct (dir n c' a t); auto.

    pose proof (stEq c0 c0Def c0_ne_c c0_child) as stEq'.
    rewrite stEq'.
    constructor.
    generalize IHt c0Def c0_child; clear; firstorder.
    intros c' c'Def c'_ne_c0 c'_child.
    destruct (classic (c' = c)) as [c'_eq_c | c'_ne_c].
    rewrite c'_eq_c in *.
    destruct resp as [markm | recvm].
    pose proof (sendCCond nDef cDef c_child markm) as [_ toMOld].
    assert (c_ne_c0: c0 <> c) by auto.
    specialize (toMOld c0 c0Def c_ne_c0 c0_child).
    rewrite <- c'_eq_c in *; clear c'_eq_c.
    pose proof (sendmChange (dt nDef c'Def c'_child) markm) as sth.
    rewrite sth.
    destruct (dir n c0 a t); destruct (to m); unfold sle in *; auto.

    pose proof (pRecvDowngrade nDef cDef c_child recvm) as sth_gt.
    assert (gtz: slt In (dir n c a t)) by
        (destruct (dir n c a (S t)); destruct (dir n c a t); unfold slt in *; auto).
    pose proof (IHt c0 c0Def c0_child) as [_ sth1].
    specialize (sth1 c c'Def c'_ne_c0 c_child).
    unfold slt in *; unfold sle in *; destruct (dir n c a (S t));
    destruct (dir n c0 a t); destruct (dir n c a t); auto.

    specialize (stEq c' c'Def c'_ne_c c'_child).
    rewrite stEq.
    generalize IHt c0_child c'Def c0Def c'_ne_c0 c'_child; clear; firstorder.

    assert (same: forall c, defined c -> parent c n -> dir n c a (S t) = dir n c a t).
    intros c cDef c_child.
    assert (eqOrNot: {dir n c a (S t) = dir n c a t} + {dir n c a (S t) <> dir n c a t})
           by decide equality.
    destruct eqOrNot as [eq|not].
    assumption.
    pose proof (change (@dt n c nDef cDef c_child) not) as ppp.
    generalize notEx nDef cDef c_child ppp; clear; firstorder.

    intros c cDef c_child.
    constructor.
    specialize (same c cDef c_child).
    rewrite same.
    generalize IHt cDef c_child; clear; firstorder.

    intros c' c'Def. intros.
    pose proof (same c' c'Def H0) as dunk.
    rewrite dunk.
    pose proof (same c cDef c_child) as dukn.
    rewrite dukn in *.
    generalize IHt cDef c'Def c_child H H0; clear; firstorder.
  Qed.

  Theorem compat:
    forall {n}, defined n -> forall a t {c}, defined c -> parent c n ->
                        sle (state c a t) (state n a t) /\
                        forall {c'}, defined c' -> c' <> c -> parent c' n -> sle (state c' a t)
                                                                   match state c a t with
                                                                     | Mo => In
                                                                     | Sh => Sh
                                                                     | In => Mo
                                                                   end.
  Proof.
    intros n nDef a t c cDef c_child.
    pose proof (compatible nDef a t cDef c_child) as base.
    constructor.
    destruct base as [dr _].
    pose proof (conservative nDef cDef c_child a t) as dLe.
    apply (sle_sle_sle dLe dr).
    destruct base as [_ others].
    intros c' c'Def c'_ne p_c'.
    specialize (others c' c'Def c'_ne p_c').
    pose proof (conservative nDef cDef c_child a t) as st.
    pose proof (conservative nDef c'Def p_c' a t) as st'.
    unfold sle in *; destruct (state c' a t); destruct (state c a t);
    destruct (dir n c' a t); destruct (dir n c a t); auto.
  Qed.

  Theorem descSle: forall {c p}, defined c -> defined p -> descendent c p -> forall {a t},
                                                                               sle (state c a t) (state p a t).
  Proof.
    intros c p defC defP c_p a t.
    induction c_p.
    pose proof (compat defP a t defC H) as [use _].
    assumption.
    assert (eq: state x a t = state x a t) by reflexivity.
    apply (sle_eq eq).
    pose proof (rt_trans Tree parent y z hier c_p2 defP) as defY.
    specialize (IHc_p1 defC defY).
    specialize (IHc_p2 defY defP).
    apply (sle_sle_sle IHc_p1 IHc_p2).
  Qed.

  Theorem nonDescCompat: forall {c1 c2},
                           defined c1 -> defined c2 ->
                           ~ descendent c1 c2 -> ~ descendent c2 c1 ->
                           forall {a t},
                             sle (state c2 a t)
                                 match state c1 a t with
                                   | Mo => In
                                   | Sh => Sh
                                   | In => Mo
                                 end.
  Proof.
    intros c1 c2 defC1 defC2 c1_no_c2 c2_no_c1.
    pose proof (hasFork defC1 defC2 c1_no_c2 c2_no_c1) as forkFull.
    destruct forkFull as [fork [defF [[d1 [defD1 [d1_fork [c1_d1 c2_no_d1]]]] [d2 [defD2 [d2_fork [c1_no_d2 c2_d1]]]]] ]].
    intros a t.
    assert (le1: sle (state c1 a t) (state d1 a t)) by (apply descSle; firstorder).
    assert (le2: sle (state c2 a t) (state d2 a t)) by (apply descSle; firstorder).
    assert (d1_ne_d2: d2 = d1 -> False) by (
             intros d1_eq_d2; rewrite d1_eq_d2 in *; firstorder).
    pose proof (compat defF a t defD1 d1_fork) as [_ useful].
    specialize (useful d2 defD2 d1_ne_d2 d2_fork).
    unfold sle in *; destruct (state c1 a t); destruct (state c2 a t);
    destruct (state d1 a t); destruct (state d2 a t); auto.
  Qed.

  Theorem allDirLower: forall {p},
                         defined p ->
                         forall {co a t s},
                           (forall c, defined c -> parent c p -> sle (dir p c a t) s) ->
                           co <> p -> descendent co p -> sle (state co a t) s.
  Proof.
    intros p defP co a t s noDir co_ne_p co_p.
    pose proof (clos_rt_rtn1 Tree parent co p co_p) as trans.
    destruct trans.
    assert (co = co) by reflexivity; firstorder.
    pose proof (clos_rtn1_rt Tree parent co y trans) as co_y.
    clear trans; fold descendent in *.
    pose proof (rt_step Tree parent y z H) as y_z.
    pose proof (rt_trans Tree parent y z hier y_z defP) as y_hier.
    specialize (noDir y y_hier H).
    pose proof (rt_trans Tree parent co y hier co_y y_hier) as co_hier.
    pose proof (@descSle co y co_hier y_hier co_y a t) as useful.
    pose proof (conservative defP y_hier H a t) as final.
    pose proof (sle_sle_sle useful final) as f2.
    apply (sle_sle_sle f2 noDir).
  Qed.
End mkCompat.
