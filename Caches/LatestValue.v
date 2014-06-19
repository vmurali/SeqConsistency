Require Import DataTypes Useful Channel Cache Compatible L1 Coq.Logic.Classical
Coq.Relations.Operators_Properties Coq.Relations.Relation_Operators List MsiState L1.
(*Require List.*)

Module Type LatestValueAxioms (dt: DataTypes) (ch: ChannelPerAddr dt).
  Import dt ch.

  Axiom toChild: forall {n a t p m}, defined n -> defined p ->
                   parent n p -> 
                   mark mch p n a t m -> from m = MsiState.In -> dataM m = data p a t.
  Axiom fromParent: forall {n a t p m}, defined n -> defined p ->
                      parent n p -> 
                      recv mch p n a t m -> from m = MsiState.In -> data n a (S t) = dataM m.
  Axiom toParent: forall {n a t c m}, defined n -> defined c ->
                     parent c n ->
                     mark mch c n a t m -> slt Sh (from m) -> dataM m = data c a t.
  Axiom fromChild: forall {n a t c m}, defined n -> defined c ->
                     parent c n ->
                     recv mch c n a t m -> slt Sh (from m) -> data n a (S t) = dataM m.

  Axiom initLatest: forall a, data hier a 0 = initData a /\ state hier a 0 = Mo.

  Axiom deqImpData: forall {a n t i}, defined n -> deqR a n i t ->
                                    desc (reqFn a n i) = St ->
                                    data n a (S t) = dataQ (reqFn a n i).

  Axiom changeData:
    forall {n a t}, defined n ->
      data n a (S t) <> data n a t ->
      (exists m, (exists p, defined p /\ parent n p /\ recv mch p n a t m /\ from m = MsiState.In) \/
                 (exists c, defined c /\ parent c n /\ recv mch c n a t m /\
                            slt Sh (from m))) \/
      exists i, deqR a n i t /\ desc (reqFn a n i) = St.


  Axiom deqImpNoSend: forall {c a i t}, defined c -> deqR a c i t -> 
                                      forall {m p}, defined p ->
                                                    ~ mark mch c p a t m.
End LatestValueAxioms.

Module LatestValueTheorems (dt: DataTypes) (ch: ChannelPerAddr dt) (c: BehaviorAxioms dt ch)
       (l1: L1Axioms dt) (comp: CompatBehavior dt ch) (lv: LatestValueAxioms dt ch): L1Theorems dt l1.
  Module mbt := mkBehaviorTheorems dt ch c.
  Module cbt := mkCompat dt ch comp c.
  Import dt ch c l1 comp lv mbt cbt.


  Theorem uniqM:
    forall {c a t}, defined c ->
      leaf c ->
      state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = MsiState.In.
  Proof.
    intros c a t defC leaf_c cM co defCo leaf_co c_ne_co.
    pose proof (noLeafsDesc leaf_c leaf_co c_ne_co) as desc1.
    assert (co_ne_c: co <> c) by auto.
    pose proof (noLeafsDesc leaf_co leaf_c co_ne_c) as desc2.
    pose proof (@nonDescCompat c co defC defCo desc1 desc2 a t) as st.
    rewrite cM in st.
    unfold sle in *; destruct (state co a t); firstorder.
  Qed.

  Theorem parentLeafFalse: forall {c p}, leaf c -> parent p c -> False.
  Proof.
    intros c p leafC p_c.
    unfold leaf in *; unfold parent in *.
    destruct c.
    destruct l0.
    unfold List.In in *.
    assumption.
    assumption.
  Qed.

  Theorem leafGood: forall {p n a t}, defined p -> defined n -> parent n p ->
                                      slt MsiState.In (dir p n a t) -> slt (state n a t) Mo ->
                                      forall {c i}, 
                                        defined c ->
                                        deqR a c i t -> desc (reqFn a c i) = St ->
                                        False.
  Proof.
    unfold not; intros p n a t defP defN n_p pGtI nLtM c i defC deqSt isSt.
    pose proof (deqLeaf deqSt) as leafC.
    pose proof (processDeq deqSt) as st; simpl in st.
    destruct (classic (descendent c p)) as [c_p | c_ne_p].
    destruct (classic (descendent c n)) as [c_n | c_ne_n].
    pose proof (@descSle c n defC defN c_n a t) as low.
    rewrite isSt in st.
    rewrite st in low.
    apply (slt_slei_false nLtM low).
    pose proof (clos_rt_rtn1 Tree parent c p c_p) as trans.
    destruct trans.
    apply (parentLeafFalse leafC n_p).
    pose proof (clos_rtn1_rt Tree parent c y trans) as c_y.
    pose proof (rt_step Tree parent y z H) as y_z.
    pose proof (rt_trans Tree parent y z hier y_z defP) as defY.
    clear trans y_z; fold descendent in *.
    assert (y_ne_n: n = y -> False).
    intros y_eq_n.
    rewrite y_eq_n in *.
    firstorder.
    pose proof (compatible defP a t defY H) as [_ good].
    specialize (good n defN y_ne_n n_p).
    pose proof (@descSle c y defC defY c_y a t) as low.
    rewrite isSt in st.
    rewrite st in low.
    pose proof (conservative defP defY H a t) as stuff.
    unfold sle in *; destruct (dir z y a t); destruct (dir z n a t); 
    destruct (state y a t); auto.
    assert (sec: ~ descendent p c).
    unfold not; intros p_c.
    pose proof (clos_rt_rtn1 Tree parent p c p_c) as trans.
    destruct trans.
    firstorder.
    apply (parentLeafFalse leafC H).
    pose proof (@nonDescCompat c p defC defP c_ne_p sec a t) as contra.
    rewrite isSt in st.
    rewrite st in contra.
    pose proof (compatible defP a t defN n_p) as [good _].
    destruct (dir p n a t); destruct (state p a t); unfold slt in *; unfold sle in *;
    auto.
  Qed.

  Theorem leafGood2: forall {p n a t}, defined p -> defined n -> parent n p ->
                                       forall {m}, mark mch p n a t m ->
                                                   forall {c i}, 
                                                     defined c ->
                                                     deqR a c i t -> desc (reqFn a c i) = St ->
                                                     False.
  Proof.
    unfold not; intros p n a t defP defN n_p m markm c i defC deqSt isSt.
    pose proof (pSendUpgrade defP defN n_p markm) as dir_n_lt_M.
    pose proof (sendCCond defP defN n_p markm) as [st_hg othersCompat].
    pose proof (sendmChange (dt defP defN n_p) markm) as rew.
    rewrite <- rew in *; clear rew.
    pose proof (deqLeaf deqSt) as leafC.
    pose proof (processDeq deqSt) as st; simpl in st.
    destruct (classic (descendent c p)) as [c_p | c_ne_p].
    destruct (classic (descendent c n)) as [c_n | c_ne_n].
    pose proof (@descSle c n defC defN c_n a t) as low.
    pose proof (conservative defP defN n_p a t) as sth.
    rewrite isSt in st.
    rewrite st in *.
    destruct (state n a t); destruct (dir p n a t); destruct (dir p n a (S t));
    unfold sle in *; unfold slt in *; auto.
    pose proof (clos_rt_rtn1 Tree parent c p c_p) as trans.
    destruct trans.
    apply (parentLeafFalse leafC n_p).
    pose proof (clos_rtn1_rt Tree parent c y trans) as c_y.
    pose proof (rt_step Tree parent y z H) as y_z.
    pose proof (rt_trans Tree parent y z hier y_z defP) as defY.
    clear trans y_z; fold descendent in *.
    assert (y_ne_n: y = n -> False).
    intros y_eq_n.
    rewrite y_eq_n in *.
    firstorder.
    specialize (othersCompat y defY y_ne_n H).
    pose proof (@descSle c y defC defY c_y a t) as low.
    pose proof (conservative defP defY H a t) as stuff.
    rewrite isSt in st.
    rewrite st in *.
    unfold sle in *; unfold slt in *; destruct (dir z n a (S t)); destruct (dir z n a t);
    destruct (dir z y a t); destruct (state y a t); auto.
    assert (sec: ~ descendent p c).
    unfold not; intros p_c.
    pose proof (clos_rt_rtn1 Tree parent p c p_c) as trans.
    destruct trans.
    firstorder.
    apply (parentLeafFalse leafC H).
    pose proof (@nonDescCompat c p defC defP c_ne_p sec a t) as contra.
    rewrite isSt in st.
    rewrite st in contra.
    unfold sle in *; unfold slt in *; destruct (dir p n a t); destruct (dir p n a (S t));
    destruct (state p a t); auto.
  Qed.

  Theorem leafGood3: forall {p n a t}, defined p -> defined n -> parent n p ->
                                       forall {m}, mark mch n p a t m ->
                                                   forall {c i}, 
                                                     defined c ->
                                                     deqR a c i t -> desc (reqFn a c i) = St ->
                                                     False.
  Proof.
    unfold not; intros p n a t defP defN n_p m markm c i defC deqSt isSt.
    destruct (classic (c = n)) as [eq|notEq].
    rewrite eq in *.
    apply (deqImpNoSend defN deqSt defP markm).
    destruct (classic (descendent c n)) as [c_n | c_no_n].
    pose proof (@sendPCond n a t p defN defP n_p m markm) as dirLower.
    pose proof (allDirLower defN dirLower notEq c_n) as condToM.
    pose proof (cSendDowngrade defP defN n_p markm) as dgd.
    pose proof (sendmChange (st defP defN n_p) markm) as stEq.
    rewrite stEq in dgd.
    pose proof (processDeq deqSt) as eqSth; simpl in *.
    rewrite isSt in eqSth.
    rewrite eqSth in *.
    destruct (state n a t); destruct (to m); unfold slt in *; unfold sle in *; auto.
    assert (n_no_c: ~ descendent n c).
    unfold not; intros n_c.
    pose proof (clos_rt_rtn1 Tree parent n c n_c) as trans.
    destruct trans.
    assert (n = n) by reflexivity; firstorder.
    pose proof (deqLeaf deqSt) as leaf_z.
    unfold parent in *; unfold leaf in *. destruct z. destruct l0.
    unfold List.In in H. assumption.
    assumption.
    pose proof (@nonDescCompat n c defN defC n_no_c c_no_n a t) as stNow.
    pose proof (cSendDowngrade defP defN n_p markm) as dgd.
    pose proof (processDeq deqSt) as eqSth; simpl in *;
    rewrite isSt in eqSth.
    rewrite eqSth in *.
    unfold sle in *; unfold slt in *; destruct (state n a t); destruct (state n a (S t));
    auto.
  Qed.

  Theorem allLatestValue:
    forall {a t n}, defined n ->
                    sle Sh (state n a t) ->
                    (forall {c}, defined c -> parent c n -> sle (dir n c a t) Sh) ->
                    (data n a t = initData a /\
                     forall {ti}, 0 <= ti < t ->
                                  forall {ci ii}, defined ci ->
                                                  ~ (deqR a ci ii ti /\
                                                     desc (reqFn a ci ii) = St)) \/
    (exists cb ib tb, defined cb /\ tb < t /\ deqR a cb ib tb /\ desc (reqFn a cb ib) = St /\
                      data n a t = dataQ (reqFn a cb ib) /\
                      forall {ti}, tb < ti < t ->
                                   forall {ci ii},
                                     defined ci ->
                                     ~ (deqR a ci ii ti /\
                                        desc (reqFn a ci ii) = St)
    ).
    Proof.
      intros a.
      pose (fun t => forall n,
              defined n ->
                    sle Sh (state n a t) ->
                    (forall {c}, defined c -> parent c n -> sle (dir n c a t) Sh) ->
                    (data n a t = initData a /\
                     forall {ti}, 0 <= ti < t ->
                                  forall {ci ii}, defined ci ->
                                                  ~ (deqR a ci ii ti /\
                                                     desc (reqFn a ci ii) = St)) \/
    (exists cb ib tb, defined cb /\ tb < t /\ deqR a cb ib tb /\ desc (reqFn a cb ib) = St /\
                      data n a t = dataQ (reqFn a cb ib) /\
                      forall {ti}, tb < ti < t ->
                                   forall {ci ii},
                                     defined ci ->
                                     ~ (deqR a ci ii ti /\
                                        desc (reqFn a ci ii) = St)
           )) as P.
      pose proof (initLatest a) as [hierInit hierM].
      apply (@ind P).
      unfold P in *; clear P.
      intros n defN stCond dirCond.
      destruct (classic (n = hier)) as [eq|notEq].
      rewrite eq.
      rewrite hierInit.
      constructor. constructor. reflexivity.
      intros ti [_ bad].
      assert (f: False) by omega.
      firstorder.
      pose proof (rt_refl Tree parent hier) as defHier.
      pose proof (@initCompat hier) as dir0.
      pose proof (clos_rt_rtn1 Tree parent n hier defN) as trans.
      pose proof @conservative as cons.
      pose proof @descSle as descSle.
      unfold defined in *.
      destruct trans.
      firstorder.
      pose proof (clos_rtn1_rt Tree parent n y trans) as n_y.
      pose proof (rt_step Tree parent y z H) as defY.
      clear dirCond trans; fold descendent in *.
      specialize (dir0 y defHier defY H a).
      pose proof (cons z y defHier defY H a 0) as sleUse.
      pose proof @descSle n y defN defY n_y a 0 as contra.
      rewrite dir0 in sleUse.
      unfold sle in *; destruct (state n a 0); destruct (state y a 0); firstorder.

      unfold P in *; clear P.
      intros t SIHt n defN condSt condDir.

      destruct (classic (sle Sh (state n a t) /\
                         forall c, defined c -> parent c n -> sle (dir n c a t) Sh))
               as [[condSt' condDir']|prevNotLatest].

      assert (triv: t <= t) by omega.
      specialize (SIHt t triv n defN condSt' condDir'); clear triv.


      assert (noneElse: forall co, defined co -> leaf co -> co <> n -> sle (state co a t) Sh).
      intros co defCo leafco co_ne_n.
      destruct (classic (descendent co n)) as [desc|noDesc].
      apply (allDirLower defN condDir' co_ne_n desc).


      assert (not_n_co: ~ descendent n co).
      unfold not; intros n_co.
      assert (no_co_parent: forall p, ~ parent p co) by
          (unfold not; intros p p_co; unfold leaf in *; unfold parent in *;
                                      unfold List.In in *; destruct co; destruct l0; auto).
      pose proof (clos_rt_rtn1 Tree parent n co n_co) as trans.
      destruct trans.
      assert (n = n) by reflexivity; firstorder.
      firstorder.

      pose proof (@nonDescCompat n co defN defCo not_n_co noDesc a t) as condState.
      destruct (state n a t); unfold sle in *; destruct (state co a t); auto.



      assert (noStore: forall co, defined co ->
                                  co <> n -> forall i,
                                               ~ (deqR a co i t /\
                                                  desc (reqFn a co i) = St
             )).
      unfold not; intros co defCo co_ne_n i [deqSt isSt].
      pose proof (deqLeaf deqSt) as leafCo.
      specialize (noneElse co defCo leafCo co_ne_n).
      pose proof (processDeq deqSt) as use; simpl in use.
      rewrite isSt in use.
      rewrite use in noneElse; unfold sle in *; auto.


      destruct (classic (exists i, deqR a n i t /\ 
               desc (reqFn a n i) = St)) as [[i [deqSt isSt]] | noNStore].

      pose proof (deqImpData defN deqSt) as st.
      rewrite isSt in st.
      rewrite st.
      assert (triv: t < S t) by omega.
      assert (triv2: forall ti, t < ti < S t -> False) by (intros ti cond; omega).
      right.
      exists n; exists i; exists t.
      generalize defN triv deqSt isSt st triv2; clear; firstorder.
      reflexivity.


      assert (good: forall c i, defined c ->
                                ~ (deqR a c i t /\ 
                                   desc (reqFn a c i) = St)).
      unfold not. intros c i defC [deqc isSt].
      destruct (classic (c = n)) as [eq|notEq].
      rewrite eq in *; generalize noNStore deqc isSt; clear; firstorder.
      generalize noStore defC notEq deqc isSt; clear; firstorder.


      destruct (classic (data n a (S t) = data n a t)) as [dataEq| dataNeq].
      rewrite dataEq.

      destruct SIHt as [[initi condInit]|[resti condResti]].
      left.
      constructor. assumption.
      intros ti cond.
      assert (cases: 0 <= ti < t \/ ti = t) by omega.
      destruct cases as [ind|rew].
      specialize (condInit ti ind).
      assumption.
      rewrite rew.
      assumption.

      destruct condResti as [ib [tb [defCb [tb_lt_t [deqSt [isSt [dEq rest]]]]]]].
      right.
      exists resti; exists ib; exists tb.
      constructor. assumption.
      constructor.
      omega.
      constructor.
      assumption.
      constructor.
      assumption.
      constructor.
      assumption.
      intros ti cond.
      assert (cases: tb < ti < t \/ ti = t) by omega.
      destruct cases as [ind|rew].
      
      apply (rest ti ind).
      rewrite rew.
      assumption.


      pose proof (changeData defN dataNeq) as someChange.
      destruct someChange as [[m [[p [defP [n_p [recvm mIn]]]] |
                                  [c [defC [c_n [recvm mNotIn]]]]]] | bad].


      pose proof (cRecvmCond defP defN n_p recvm) as currSt.
      rewrite <- currSt in condSt'; rewrite mIn in condSt'.
      unfold sle in condSt'; firstorder.

      pose proof (recvmCond defN defC c_n recvm) as currSt.
      specialize (condDir' c defC c_n).
      rewrite currSt in mNotIn.
      pose proof (slt_slei_false mNotIn condDir') as f.
      firstorder.

      generalize noNStore bad; clear; firstorder.

      destruct (classic (state n a t = MsiState.In \/ exists c, defined c /\ parent c n /\
                                                       slt Sh (dir n c a t)))
               as [hard | easy].
      clear prevNotLatest.

      destruct hard as [stIn | [c [defC [c_n dirM]]]].

      assert (lt: slt (state n a t) (state n a (S t))) by
          (rewrite stIn; unfold sle in *; unfold slt in *; destruct (state n a (S t));
           auto).
      assert (chnge: state n a (S t) <> state n a t) by
          (destruct (state n a (S t)); destruct (state n a t); unfold slt in *;
                                                               unfold sle in *;
                                                               auto; discriminate).
      destruct (classic (exists p, defined p /\ parent n p)) as [[p [defP n_p]] | noP].
      pose proof (change (st defP defN n_p) chnge) as [[m markm] | [m recvm]].
      pose proof (cSendDowngrade defP defN n_p markm) as contra.
      pose proof (slt_slti_false lt contra) as f.
      firstorder.










      pose proof (recvImpMark recvm) as [ts [ts_le_t markm]].
      pose proof (@pSendNonI p n defP defN n_p m ts t a markm recvm) as pHigh.
      pose proof (@cRecvNonM p n defP defN n_p m ts t a markm recvm) as cLow.
      assert (cLow1: forall t0, ts < t0 <= t -> slt (state n a t0) Mo) by
          ( intros t0 cond; assert (H: ts <= t0 <= t) by omega; apply (cLow t0 H)).
      assert (cLow2: slt (state n a ts) Mo) by (assert (H: ts <= ts <= t) by omega;
                                                apply (cLow ts H)).

      assert (noDeq1: forall t0, ts < t0 <= t ->
                                 forall c i, defined c -> ~ (deqR a c i t0
                                                            /\ 
                                                            desc (reqFn a c i) = St)).
      intros t0 cond.
      specialize (pHigh t0 cond).
      specialize (cLow1 t0 cond).
      pose proof (@leafGood p n a t0 defP defN n_p pHigh cLow1) as H.
      generalize H; clear; firstorder.

      pose proof (@leafGood2 p n a ts defP defN n_p m markm) as noDeq2.

      assert (goodT: forall t0, ts <= t0 <= t ->
                                forall c i, defined c -> ~ (deqR a c i t0 /\
                                                            desc (reqFn a c i) = St)).
      intros t0 cond.
      assert (H: ts < t0 <= t \/ t0 = ts) by omega.
      destruct H as [c1|c2].
      apply (noDeq1 t0 c1).
      rewrite c2 in *.
      generalize noDeq2; clear; firstorder.


      pose proof (cRecvmCond defP defN n_p recvm) as stEq.
      rewrite <- stEq in stIn.
      pose proof (fromParent defN defP n_p recvm stIn) as dataEq.
      pose proof (toChild defN defP n_p markm stIn) as dataEq2.
      rewrite <- dataEq in dataEq2.
      rewrite dataEq2.

      pose proof (sendCCond defP defN n_p markm) as [one two].
      pose proof (pSendUpgrade defP defN n_p markm) as upg.
      pose proof (sendmChange (dt defP defN n_p) markm) as ch.
      rewrite ch in upg.
      assert (p1: sle Sh (state p a ts)) by
          ( unfold sle in *; unfold slt in *; destruct (to m); destruct (state p a ts);
            destruct (dir p n a ts); auto).
      assert (p2: forall c', defined c' -> parent c' p ->
                         sle (dir p c' a ts) Sh).
      intros c' defC' c'_p.


      destruct (classic (c' = n)) as [eq|not].
      pose proof (cRecvRespPrevState defP defN n_p recvm markm) as stDir.
      rewrite <- stEq in stDir.
      rewrite stIn in stDir.
      rewrite eq.
      rewrite <- stDir.
      unfold sle; auto.

      specialize (two c' defC' not c'_p).
      unfold sle in *; unfold slt in *; destruct (to m); destruct (dir p n a ts);
      destruct (dir p c' a ts); auto.

      specialize (SIHt ts ts_le_t p defP p1 p2).
      destruct (SIHt) as [[initi condInit] | [resti condRest]].
      left.
      constructor. assumption. 

      intros ti cond; assert (H: 0 <= ti < ts \/ ts <= ti <= t ) by omega; 
      destruct H as [ind|tough].

      apply (condInit ti ind).
      apply (goodT ti tough).


      right.
      destruct condRest as [ib [tb [defCb [tb_lt_ts [deqSt [isSt [dtEq rest]]]]]]].
      exists resti; exists ib; exists tb.
      constructor. assumption. constructor.
      assert (tb < S t) by omega. assumption.
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      intros ti cond; assert (H: tb < ti < ts \/ ts <= ti <= t) by omega;
      destruct H as [ind|tough].
      apply (rest ti ind).
      apply (goodT ti tough).









      assert (contra: forall p, defined p -> ~ parent n p) by firstorder.
      specialize (@noParentSame n a t defN contra).
      firstorder.


      specialize (condDir c defC c_n).

      assert (gt: slt (dir n c a (S t)) (dir n c a t)) by
          (unfold slt in *; unfold sle in *; destruct (dir n c a (S t));
           destruct (dir n c a t); auto; discriminate).
      assert (chnge: dir n c a (S t) <> dir n c a t) by
          (destruct (dir n c a (S t)); destruct (dir n c a t); unfold slt in *;
                                                               unfold sle in *;
                                                               auto; discriminate).

      pose proof (change (dt defN defC c_n) chnge) as [[m markm] | [m recvm]].
      pose proof (pSendUpgrade defN defC c_n markm) as contra.
      pose proof (slt_slti_false gt contra) as f.
      firstorder.


      pose proof (recvImpMark recvm) as [ts [ts_le_t markm]].
      pose proof (@pRecvNonI n c defN defC c_n m ts t a markm recvm) as pHigh.
      pose proof (@cSendNonM n c defN defC c_n m ts t a markm recvm) as cLow.
      assert (pHigh1: forall t0, ts < t0 <= t -> slt MsiState.In (dir n c a t0)) by
          ( intros t0 cond; assert (H: ts <= t0 <= t) by omega; apply (pHigh t0 H)).
      assert (pHigh2: slt MsiState.In (dir n c a ts)) by (assert (H: ts <= ts <= t) by omega;
                                                apply (pHigh ts H)).

      assert (noDeq1: forall t0, ts < t0 <= t ->
                                 forall c i, defined c -> ~ (deqR a c i t0 /\
                                                             desc (reqFn a c i) = St)).
      intros t0 cond.
      specialize (cLow t0 cond).
      specialize (pHigh1 t0 cond).
      pose proof (@leafGood n c a t0 defN defC c_n pHigh1 cLow) as H.
      generalize H; clear; firstorder.


      pose proof (@leafGood3 n c a ts defN defC c_n m markm) as noDeq2.

      assert (goodT: forall t0, ts <= t0 <= t ->
                                forall c i, defined c -> ~ (deqR a c i t0 /\
                                                            desc (reqFn a c i) = St)).
      intros t0 cond.
      assert (H: ts < t0 <= t \/ t0 = ts) by omega.
      destruct H as [c1|c2].
      apply (noDeq1 t0 c1).
      rewrite c2 in *.
      generalize noDeq2; clear; firstorder.




      pose proof (recvmCond defN defC c_n recvm) as stEq.
      rewrite <- stEq in dirM.
      pose proof (fromChild defN defC c_n recvm dirM) as dataEq.
      pose proof (toParent defN defC c_n markm dirM) as dataEq2.
      rewrite <- dataEq in dataEq2.
      rewrite dataEq2.

      pose proof (@sendPCond c a ts n defC defN c_n m markm) as sth.
      pose proof (recvmChange (dt defN defC c_n) recvm) as ch.
      rewrite ch in condDir.
      pose proof (cSendDowngrade defN defC c_n markm) as dwn.


      assert (p2: forall c0, defined c0 -> parent c0 c -> sle (dir c c0 a ts) Sh).
      intros c0 defC0 c0_c; specialize (sth c0 defC0 c0_c);
      destruct (to m); destruct (dir c c0 a ts); unfold sle in *; unfold slt in *;
      auto.

      assert (p1: sle Sh (state c a ts)) by
          ( unfold sle in *; unfold slt in *; destruct (state c a (S ts));
            destruct (state c a ts); auto).

      specialize (SIHt ts ts_le_t c defC p1 p2).


      destruct SIHt as [[initi condInit] | [resti condRest]].
      left.
      constructor. assumption.
      intros ti cond; assert (H: 0 <= ti < ts \/ ts <= ti <= t ) by omega; 
      destruct H as [ind|tough].

      apply (condInit ti ind).
      apply (goodT ti tough).

      right.
      destruct condRest as [ib [tb [defCb [tb_lt_ts [deqSt [isSt [dtEq rest]]]]]]].
      exists resti; exists ib; exists tb.
      constructor. assumption. constructor.
      assert (tb < S t) by omega. assumption.
      constructor. assumption.
      constructor. assumption.
      constructor. assumption.
      intros ti cond; assert (H: tb < ti < ts \/ ts <= ti <= t) by omega;
     destruct H as [ind|tough].
      apply (rest ti ind).
      apply (goodT ti tough).





      assert (ex: forall c, defined c -> parent c n -> ~ slt Sh (dir n c a t)) by
          firstorder.
      assert (ex': forall c, defined c -> parent c n -> sle (dir n c a t) Sh) by
          ( intros c defC c_n; unfold sle in *; specialize (ex c defC c_n);
            unfold slt in *; destruct (dir n c a t); auto).
      assert (ex2: state n a t <> MsiState.In) by firstorder.
      assert (ex2': sle Sh (state n a t)) by (destruct (state n a t); unfold sle in *;
                                                                      auto).
      firstorder.

    Qed.

  Theorem latestValue:
  forall {c a t},
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    (data c a t = initData a /\
     forall {ti}, 0 <= ti < t -> forall {ci ii},
                                   defined ci ->
                                   ~ (deqR a ci ii ti /\
                                      desc (reqFn a ci ii) = St)) \/
    (exists cb ib tb, defined cb /\ tb < t /\ deqR a cb ib tb /\ desc (reqFn a cb ib) = St /\
                      data c a t = dataQ (reqFn a cb ib) /\
                      forall {ti}, tb < ti < t ->
                                   forall {ci ii},
                                     defined ci ->
                                     ~ (deqR a ci ii ti /\
                                        desc (reqFn a ci ii) = St)
    ).
  Proof.
    intros c a t cDef leafC more.
    assert (cond: forall {c'}, defined c' -> parent c' c -> sle (dir c c' a t) Sh).
    intros c' defC' c'_c; unfold leaf in *; unfold parent in *.
    destruct c.
    destruct l0.
    unfold List.In in *.
    firstorder.
    firstorder.
    pose proof (allLatestValue cDef more cond) as useful.
    assumption.
  Qed.

  Definition deqOrNot := l1.deqOrNot.
End LatestValueTheorems.
