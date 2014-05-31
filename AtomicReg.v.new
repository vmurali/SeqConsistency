Require Import DataTypes StoreAtomicity Case NamedTrans Useful Tree.

Set Implicit Arguments.

Section ForAddr.
  Variable a: Addr.

  Record State := { mem: Data;
                    next: Tree -> Index
                  }.
  
  Inductive AtomicTrans s: State -> Set :=
  | Req: forall c, AtomicTrans s (Build_State
                                    (match desc (reqFn a c (next s (p_node c))) with
                                       | Ld => mem s
                                       | St => dataQ (reqFn a c (next s (p_node c)))
                                     end)
                                    (fun t => match decTree t (p_node c) with
                                                | left _ => S (next s t)
                                                | _ => next s t
                                              end))
  | Idle: AtomicTrans s s.
  
  Variable respFn: Time -> option Resp.
  Variable sa: StoreAtomicity a respFn.

  Definition AtomicList := TransList AtomicTrans (Build_State (initData a) (fun t => 0)).

  Definition getTransNext n s (al: AtomicList n s) :=
    match respFn n with
      | Some r => Build_NextTrans _ _ _ (Req s (procR r))
      | None => Build_NextTrans _ _ _ (Idle s)
    end.

  Lemma nextLe t c: next (getTransSt getTransNext t) c <=
                    next (getTransSt getTransNext (S t)) c.
  Proof.
    pose (getTrans getTransNext t) as trans;
    unfold getTransSt;
    unfold getTransList;
    fold (getTransList getTransNext t); simpl.
    destruct trans; [simpl; destruct (decTree c (p_node c0)) | ]; omega.
  Qed.

  Lemma nextStarLe t1 t2 c (cond: t1 <= t2): next (getTransSt getTransNext t1) c <=
                                             next (getTransSt getTransNext t2) c.
  Proof.
    remember (t2-t1) as td; assert (H: t2 = t1 + td) by omega;
    rewrite H in *; clear t2 cond H Heqtd.
    induction td.
    assert (H: t1 + 0 = t1) by omega; rewrite H; omega.
    assert (H: t1 + S td = S (t1 + td)) by omega; rewrite H; clear H;
    pose proof (nextLe (t1 + td) c) as sth.
    omega.
  Qed.

  Lemma reqImpGt t: match getTrans getTransNext t with
                      | Req c => S (next (getTransSt getTransNext t) (p_node c)) =
                                 next (getTransSt getTransNext (S t)) (p_node c) /\
                                 forall c', c' <> p_node c ->
                                            next (getTransSt getTransNext t ) c' =
                                            next (getTransSt getTransNext (S t)) c'
                      | Idle => forall c, next (getTransSt getTransNext t ) c =
                                          next (getTransSt getTransNext (S t)) c
                    end.
  Proof.
    unfold getTransSt.
    unfold getTransList; fold (getTransList getTransNext t); simpl.
    destruct (getTrans getTransNext t).
    simpl.
    destruct (decTree (p_node c) (p_node c)).
    constructor. omega.
    intros c' c'_neq.
    destruct (decTree c' (p_node c)).
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem uniqAtomLabels:
    forall t1 t2,
      match getTrans getTransNext t1, getTrans getTransNext t2 with
        | Req c1, Req c2 =>
          p_node c1 = p_node c2 ->
          next (getTransSt getTransNext t1) (p_node c1) =
          next (getTransSt getTransNext t2) (p_node c2) ->
          t1 = t2
        | _, _ => True
      end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros c_eq n_eq.
    rewrite <- c_eq in *.
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.

    destruct sth1 as [u1 _];
      destruct sth2 as [u2 _].
    destruct opts as [eq | [lt | gt]].
    assumption.

    Ltac finish c cond :=
      pose proof (nextStarLe (p_node c) cond) as use;
      assert False by omega; intuition.
    finish c lt.
    finish c gt.

    intuition.
    intuition.
  Qed.

  Theorem localAtomOrdering:
    forall t1 t2, match getTrans getTransNext t1, getTrans getTransNext t2 with
                    | Req c1, Req c2 =>
                      p_node c1 = p_node c2 ->
                      next (getTransSt getTransNext t1) (p_node c1) <
                      next (getTransSt getTransNext t2) (p_node c2) ->
                        t1 < t2
                    | _, _ => True
                  end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros c_eq n_lt.
    rewrite <- c_eq in *.
    destruct sth1 as [u1 _]; destruct sth2 as [u2 _].
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct opts as [eq | [lt | gt]].
    rewrite eq in *; assert False by omega; intuition.
    intuition.
    pose proof (nextStarLe (p_node c) gt) as use;
      assert False by omega; intuition.

    intuition.
    intuition.
  Qed.

  Theorem allAtomPrev t c i:
    next (getTransSt getTransNext t) c > i ->
    exists t', t' < t /\ match getTrans getTransNext t' with
                           | Req c' => c = p_node c' /\
                                       next (getTransSt getTransNext t') (p_node c') = i
                           | Idle => False
                         end.
  Proof.
    intros gt.
    induction t.
    simpl in gt.
    assert False by omega; intuition.
    pose proof (nextLe t c) as sth.
    assert (opts: next (getTransSt getTransNext (S t)) c =
                  next (getTransSt getTransNext t) c \/
                  next (getTransSt getTransNext (S t)) c >
                  next (getTransSt getTransNext t) c) by (unfold Index; omega).
    destruct opts as [e|n].
    rewrite e in gt; destruct (IHt gt) as [t' [cond rest]]; exists t'; constructor;
    [ omega | intuition].
    assert (opts: next (getTransSt getTransNext t) c = i \/
                  next (getTransSt getTransNext t) c > i \/
                  next (getTransSt getTransNext t) c < i) by (unfold Index; omega).
    destruct opts as [eq | [lt | gtt]].
    exists t; constructor.
    omega. 
    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    destruct (decTree c (p_node c0)).
    rewrite e in *; intuition.
    specialize (u2 c n0).
    assert False by omega; intuition.
    specialize (sth2 c);
      assert False by omega; intuition.

    destruct (IHt lt) as [t' cond].
    exists t'; constructor; [omega | intuition].

    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    specialize (u2 c).
    destruct (decTree c (p_node c0)).
    rewrite <- e in *.
    assert False by omega; intuition.
    specialize (u2 n0); assert False by omega; intuition.
    specialize (sth2 c); assert False by omega; intuition.
  Qed.

  Definition noCurrAtomStore t :=
    match getTrans getTransNext t with
      | Req c' =>
        let (descQ', dtQ') :=
            reqFn a c' (next (getTransSt getTransNext t) (p_node c')) in
          descQ' = St -> False
      | _ => True
    end.

  Definition noAtomStore tl t:=
    forall t', tl <= t' < t -> noCurrAtomStore t'.

  Definition matchAtomStore cm tm t :=
    let (descQm, dtQm) :=
        reqFn a cm (next (getTransSt getTransNext tm) (p_node cm)) in
    mem (getTransSt getTransNext t) = dtQm /\
    descQm = St.

  Definition lastMatchAtomStore tm t :=
    match getTrans getTransNext tm with
      | Req cm => matchAtomStore cm tm t /\
                  noAtomStore (S tm) t
      | _ => False
    end.

  Definition latestAtomValue t :=
    (mem (getTransSt getTransNext t) = initData a /\
     noAtomStore 0 t) \/
    (exists tm,
       tm < t /\ lastMatchAtomStore tm t).

  Definition atomNoPrevNonSt t :=
    noAtomStore 0 t /\
    mem (getTransSt getTransNext (S t)) = initData a /\
    noCurrAtomStore t.

  Definition atomPrevNonSt t :=
    (exists tm,
       tm < t /\
       match getTrans getTransNext tm with
         | Req cm => matchAtomStore cm tm (S t) /\
                     noAtomStore (S tm) t
         | _ => False
       end) /\
    noCurrAtomStore t.

  Definition atomSt t :=
    lastMatchAtomStore t (S t).

  Lemma latestAtomInd t (now: atomNoPrevNonSt t \/ atomPrevNonSt t \/ atomSt t):
    latestAtomValue (S t).
  Proof.
    unfold latestAtomValue.
    destruct now as [noPrevNonSt | [prevNonSt | st]].

    Case "noPrevNonSt".
    unfold atomNoPrevNonSt in *.
    left.
    constructor.
    intuition.
    unfold noAtomStore in *.
    intros t' cond.
    assert (opts: 0 <= t' < t \/ t' = t) by omega.
    destruct opts as [done | eq]; [| rewrite eq]; intuition.

    Case "prevNonSt".
    right.
    unfold atomPrevNonSt in *.
    destruct prevNonSt as [[tm [cond lm]] noCurr].
    exists tm.
    constructor.
    omega.
    unfold lastMatchAtomStore in *.
    destruct (getTrans getTransNext tm).
    constructor.
    intuition.
    unfold noAtomStore.
    intros t' cond2.
    assert (opts: S tm <= t' < t \/ t' = t) by omega.
    destruct opts as [ez|ez2].
    intuition.
    rewrite ez2 in *; intuition.
    intuition.

    Case "st".
    right.
    unfold atomSt in st.
    exists t.
    constructor.
    omega.
    intuition.
  Qed.

  Lemma latestAtomValueHolds t: latestAtomValue t.
  Proof.
    induction t.

    Case "0".
    left; constructor; [| intros t' contra; assert False by omega]; intuition.

    Case "S t".
    apply latestAtomInd.

    unfold latestAtomValue in IHt.
    unfold lastMatchAtomStore in IHt.
    unfold atomNoPrevNonSt.
    unfold noCurrAtomStore.
    unfold atomPrevNonSt.
    unfold matchAtomStore in *.
    unfold noCurrAtomStore.

    unfold atomSt.
    unfold lastMatchAtomStore.
    unfold matchAtomStore.
    unfold noAtomStore.

    unfold getTransSt at 1 3 in IHt.
    unfold getTransSt at 1 2 4 5 6 7.
    unfold getTrans at 1 3 4.
    unfold getTransList; 
      fold (getTransList getTransNext t); simpl.
    destruct (trans (getTransNext (lTrans (getTransList getTransNext t))));
      simpl in *.

    SCase "Req".
    destruct (reqFn a c (next (lSt (getTransList getTransNext t)) (p_node c))); simpl.
    destruct desc.

    SSCase "Ld".
    destruct IHt.

    SSSCase "NoPrev".
    left.
    intuition.
    discriminate.

    SSSCase "Prev".
    right; left.
    destruct (reqFn a c (next (lSt (getTransList getTransNext t)) (p_node c))).
    intuition.
    discriminate.

    SSCase "St".
    right; right.
    intuition omega.

    SCase "Idle".
    destruct IHt; intuition.
  Qed.


  Theorem storeAtomicityAtom:
    forall t,
      match getTrans getTransNext t with
        | Req c =>
          let (descQ, dtQ) := reqFn a c (next (getTransSt getTransNext t) (p_node c)) in
          match descQ with
            | Ld => latestAtomValue t
            | St => True 
          end
        | _ => True
      end.
  Proof.
    intros t.
    pose proof (latestAtomValueHolds t).
    destruct (getTrans getTransNext t).
    destruct (reqFn a c (next (getTransSt getTransNext t) (p_node c))) as [desc _].
    destruct desc.
    apply latestAtomValueHolds.
    intuition.
    intuition.
  Qed.

  Definition atomicResp s s' (t: AtomicTrans s s') :=
    match t with
      | Req c => Some (Build_Resp c (next s (p_node c))
                                  match desc (reqFn a c (next s (p_node c))) with
                                    | Ld => mem s
                                    | St => initData zero
                                  end)
      | Idle => None
    end.

  Definition sameResp r1 r2 :=
    match r1, r2 with
      | Some (Build_Resp p1 i1 d1), Some (Build_Resp p2 i2 d2) =>
        p_node p1 = p_node p2 /\ i1 = i2 /\ d1 = d2
      | Some _, None => False
      | None, Some _ => False
      | None, None => True
    end.

  Section PrevMatch.
    Variable t: nat.
    Variable prevEq: forall ti : nat,
                       ti < t -> sameResp (respFn ti) (atomicResp (getTrans getTransNext ti)).

    Definition nextTransList := getTransList getTransNext.

    Ltac assocResp :=
      unfold getTrans in *;
      unfold getTransSt in *;
      fold nextTransList in *;
      unfold getTransNext in *.

    Lemma bothSomeOrNone:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some _, Some _ => True
        | None, None => True
        | _, _ => False
      end.
    Proof.
      assocResp.
      destruct (respFn t); simpl; intuition.
    Qed.

    Lemma procSame:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp c1 _ _), Some (Build_Resp c2 _ _) => p_node c1 = p_node c2
        | _, _ => True
      end.
    Proof.
      assocResp.
      destruct (respFn t); simpl.
      destruct r; intuition.
      intuition.
    Qed.

    Lemma nextGtFalse:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 > i2 -> False
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r caseR; destruct r; simpl in *.
      intros nextGt.
      pose proof (allAtomPrev _ _ nextGt) as [t' [t'_lt_t allPrev]].
      specialize (prevEq t'_lt_t).
      assocResp.
      case_eq (respFn t').
      intros r caseR'; destruct r; rewrite caseR' in *; simpl in *.
      pose proof (uniqRespLabels sa t t') as uniq.
      rewrite caseR, caseR' in uniq.
      destruct prevEq as [_ [idEq _]].
      rewrite <- idEq in allPrev.
      assert (tEq: t = t') by (generalize allPrev uniq; clear; intuition).
      assert False by omega; intuition.
      intros caseR'; rewrite caseR' in *; intuition.
      intros caseR; simpl in *; intuition.
    Qed.

    Lemma nextLtFalse:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 < i2 -> False
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r caseR; destruct r; simpl in *.
      intros nextLt.
      pose proof (allPrevious sa t) as allPrev.
      rewrite caseR in *.
      specialize (allPrev _ nextLt).
      destruct allPrev as [t' [t'_lt_t allPrev]].
      specialize (prevEq t'_lt_t).
      assocResp.
      case_eq (respFn t').
      intros r caseR'; destruct r; rewrite caseR' in *; simpl in *.
      pose proof (uniqAtomLabels t t') as uniq.
      assocResp.
      rewrite caseR, caseR' in uniq; simpl in *.
      destruct prevEq as [_ [idEq _]].
      assert (tEq: t = t') by (generalize allPrev idEq uniq; clear;
                               unfold Index; intuition).
      assert False by omega; intuition.
      intros caseR'; rewrite caseR' in *; intuition.
      intros caseR; simpl in *; intuition.
    Qed.

    Lemma nextEq:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 = i2
        | _, _ => True
      end.
    Proof.
      pose proof nextLtFalse;
      pose proof nextGtFalse;
      repeat destructAll; try (omega); unfold Index; intuition.
    Qed.

    Lemma loadMatch:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ _ d1), Some (Build_Resp _ _ d2) =>
          d1 = d2
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r respEq; destruct r; simpl in *.
      case_eq (desc (reqFn a procR (next (lSt (nextTransList t)) (p_node procR)))).
      intros isLd.
      pose proof nextEq as nextEq.
      pose proof (storeAtomicity sa t) as atom1.
      pose proof (storeAtomicityAtom t) as atom2.
      assocResp.
      rewrite respEq in *.
      simpl in *.
      rewrite nextEq in *.
      destruct (reqFn a procR idx).
      simpl in *.
      rewrite isLd in *.
      unfold latestAtomValue in atom2.

      destruct atom1 as [no1|yes1]; destruct atom2 as [no2|yes2].

      Case "noBefore1, noBefore 2".
      destruct no1 as [u1 _]; destruct no2 as [u2 _].
      rewrite <- u1 in u2; assumption.

      Case "noBefore1, before 2".
      destruct yes2 as [tm [tm_lt_t stMatch]].
      unfold lastMatchAtomStore in stMatch.
      specialize (prevEq tm_lt_t).
      assocResp.
      destruct no1 as [_ no1].
      unfold noStore in *.
      specialize (no1 tm tm_lt_t).
      
      case_eq (respFn tm).
      intros r respmEq; destruct r; rewrite respmEq in *; simpl in *.
      unfold matchAtomStore in stMatch.
      assocResp.
      destruct prevEq as [_ [idEq _]].
      rewrite <- idEq in *.
      destruct (reqFn a procR0 idx0).
      destruct stMatch as [[u1 u2] _].
      intuition.

      intros respmEq; rewrite respmEq in *; simpl in *; intuition.

      Case "before1, noBefore 2".
      destruct yes1 as [tm [tm_lt_t' stMatch]].
      specialize (prevEq tm_lt_t').
      assert (tm_lt_t: 0 <= tm < t) by omega.
      destruct no2 as [_ no2].
      unfold noAtomStore in no2.
      unfold noCurrAtomStore in no2.
      assocResp.
      specialize (no2 tm tm_lt_t).

      case_eq (respFn tm).
      intros r respmEq; destruct r; rewrite respmEq in *; simpl in *.
      destruct prevEq as [_ [idEq _]].
      rewrite <- idEq in *.
      destruct (reqFn a procR0 idx0).
      destruct stMatch as [u1 [u2 _]].
      intuition.

      intros respmEq; rewrite respmEq in *; simpl in *; intuition.
      
      Case "before1, before 2".
      destruct yes1 as [tm1 [tm1_lt_t stMatch1]].
      destruct yes2 as [tm2 [tm2_lt_t stMatch2]].
      unfold lastMatchAtomStore in stMatch2.
      assocResp.
      pose proof (prevEq tm1_lt_t) as prev1.
      pose proof (prevEq tm2_lt_t) as prev2.
      clear prevEq.
      unfold matchAtomStore, noAtomStore, noCurrAtomStore in *;
        assocResp.

      unfold noStore in *.

      case_eq (respFn tm1); case_eq (respFn tm2).

      SCase "some tm1, some tm2".
      intros r r2Eq; destruct r; rewrite r2Eq in *;
      intros r r1Eq; destruct r; rewrite r1Eq in *; simpl in *.

      destruct prev1 as [_ [i1Eq d1Eq]].
      rewrite <- i1Eq in *;
      rewrite d1Eq in *; clear d1Eq.
      destruct prev2 as [_ [i2Eq d2Eq]].
      rewrite <- i2Eq in *;
      rewrite d2Eq in *; clear d2Eq.

      simpl in *.

      assert (opts: tm1 = tm2 \/ tm1 < tm2 \/ tm1 > tm2) by omega.
      destruct opts.

      SSCase "tm1 = tm2".
      rewrite H in *.
      rewrite r1Eq in r2Eq.
      injection r2Eq as dEq iEq pEq.
      rewrite dEq in *;
        rewrite iEq in *;
        rewrite pEq in *.
      destruct (reqFn a procR0 idx0).
      destruct stMatch1 as [u1 _];
        destruct stMatch2 as [[u2 _] _].
      rewrite <- u1 in u2;
        assumption.

      destruct H.

      SSCase "tm1 < tm2".      
      destruct (reqFn a procR1 idx1).
      destruct stMatch1 as [_ [_ noLater]].
      assert (c1: tm1 < tm2 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r2Eq in noLater.
      destruct (reqFn a procR0 idx0).
      generalize stMatch2 noLater; clear; intuition.

      SSCase "tm2 < tm1".
      destruct (reqFn a procR0 idx0).
      destruct stMatch2 as [_ noLater].
      assert (c1: S tm2 <= tm1 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r1Eq in noLater.
      simpl in *.
      rewrite <- i1Eq in *.
      destruct (reqFn a procR1 idx1).
      generalize stMatch1 noLater; clear; intuition.

      SCase "some tm1, none tm2".
      intros r2Eq r r1Eq; destruct r; rewrite r2Eq in *; rewrite r1Eq in *;
      simpl in *; intuition.

      SCase "none tm1, some tm2".
      intros r r2Eq r1Eq; destruct r; rewrite r2Eq, r1Eq in *.
      simpl in *; intuition.

      SCase "none tm1, none tm2".
      intros r2Eq r1Eq; rewrite r2Eq, r1Eq in *.
      simpl in *; intuition.

      intros r.
      simpl in *.
      pose proof nextEq as nextEq.
      assocResp.
      pose proof (storeAtomicity sa t).
      rewrite respEq in *.
      simpl in *.
      rewrite nextEq in r.
      destruct (reqFn a procR idx).
      simpl in *.
      rewrite r in *.
      auto.

      intros.
      repeat destructAll; intuition.
    Qed.

    Lemma allMatch:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp c1 i1 d1), Some (Build_Resp c2 i2 d2) =>
          i1 = i2 /\ p_node c1 = p_node c2 /\ d1 = d2
        | None, Some _ => False
        | Some _, None => False
        | None, None => True
      end.
    Proof.
      pose proof bothSomeOrNone.
      pose proof procSame.
      pose proof nextEq.
      pose proof loadMatch.

      repeat destructAll; intuition.
    Qed.
  End PrevMatch.

  Theorem obeysP: forall n,
                    sameResp (respFn n) (atomicResp (getTrans getTransNext n)).
  Proof.
    apply strong_ind.
    intros t prevEq.
    pose proof (allMatch prevEq) as sth.
    unfold sameResp.
    repeat destructAll;
    repeat f_equal; intuition.
  Qed.

  Definition getAtomicResp n := atomicResp (getTrans getTransNext n).

  Theorem respEq n: sameResp (respFn n) (getAtomicResp n).
  Proof.
    apply (obeysP n).
  Qed.

End ForAddr.

Print Assumptions respEq.