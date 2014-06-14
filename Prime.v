Set Implicit Arguments.

Require Import DataTypes StoreAtomicity AlwaysEventually NamedTrans Omega Case Useful.

Axiom cheat: forall t, t.

Section ForAddr.
  Variable Rest: Set.
  Variable initRest: Rest.
  Variable System: Rest -> Rest -> Set.
  Variable getInfo: forall r1 r2, System r1 r2 -> option (Addr * Proc * Data * Desc * Data).

  CoInductive SystemStream: Rest -> Set :=
    | SCons: forall r r', System r r' -> SystemStream r' -> SystemStream r.

  Fixpoint getNState n r (ls: SystemStream r) :=
    match ls with
      | SCons x y _ ls' => match n with
                             | 0 => (x, y)
                             | S m => getNState m ls'
                           end
    end.

  Fixpoint getNSystem' r (ls: SystemStream r) is n:
    {x: System (fst (getNState n ls))
               (snd (getNState n ls)) *
        option nat | match getInfo (fst x), snd x with
                       | Some _, Some _ => True
                       | None, None => True
                       | _, _ => False
                     end} :=
    match ls with
      | SCons _ _ t ls' => match n with
                             | 0 => exist _ (t,
                                     match getInfo t with
                                       | Some (a, p, _, _, _) => Some (is a p)
                                       | None => None
                                     end) (cheat _)
                             | S m => getNSystem'
                                        ls'
                                        match getInfo t with
                                          | Some (a, p, _, _, _) =>
                                            fun a' p' =>
                                              match decAddr a a', decProc p p' with
                                                | left _, left _ => S (is a' p')
                                                | _, _ => is a' p'
                                              end
                                          | None => fun a' p' => is a' p'
                                        end m
                           end
    end.

  Variable stm: SystemStream initRest.

  Fixpoint getNSystem n := getNSystem' stm (fun a p => 0) n.

  Definition respFn n: option Resp :=
    match getNSystem n with
      | exist (t, opti) _ => 
        match getInfo t with
          | Some (a, p, d, w, ld) => Some (Build_Resp a p (match opti with
                                                             | Some i => i
                                                             | None => 0
                                                           end)
                                                      ld)
          | None => None
        end
    end.

  Lemma semiEq n:
    match getNSystem n with
      | exist (t, _) _ =>
        match getInfo t, respFn n with
          | Some (a, p, _, w, ld), Some (Build_Resp a' p' _ d) =>
            a = a' /\ p = p' /\ ld = d
          | None, None => True
          | _, _ => False
        end
    end.
  Proof.
    unfold respFn.
    simpl.
    destruct (getNSystem n) as [[t s] _].
    destruct (getInfo t).
    destruct p.
    destruct p.
    destruct p.
    destruct p.
    destruct d0; intuition.
    intuition.
  Qed.

  CoFixpoint getReqStream r (rs: SystemStream r) :=
    match rs with
      | SCons _ _ t rs' =>
        match getInfo t with
          | Some (a, p, d, w, _) =>
            fun a' p'  =>
              match decAddr a a', decProc p p' with
                | left _, left _ =>
                  Cons (Some (Build_Req w d)) (getReqStream rs' a' p')
                | _, _ => Cons None (getReqStream rs' a' p')
              end
          | None => fun a' p' => Cons None (getReqStream rs' a' p')
        end
    end.

  Definition isSome A (x: option A) :=
    match x with
      | Some y => True
      | _ => False
    end.

  Variable alStm: forall a p, AlwaysEventually (@isSome _) (getReqStream stm a p).

  Theorem decOption A (x: option A): {isSome x} + {~ isSome x}.
  Proof.
    unfold isSome; destruct x; intuition.
  Qed.

  Definition getSome A (x: option A) (pf: isSome x): A :=
    match x as x0 return match x0 with
                           | Some _ => True
                           | None => False
                         end -> A with
      | Some a => fun _ => a
      | None => fun pf0: False => match pf0 with end
    end pf.

  Definition reqFn a p := getN (@decOption _) (@getSome _) (alStm a p).

  Lemma semiEq' n:
    match getNSystem n with
      | exist (t, opti) _ =>
        match getInfo t, opti with
          | Some (a, p, _, w, _), Some i => desc (reqFn a p i) = w
          | _, _ => True
        end
    end.
  Proof.
    apply (cheat _).
  Qed.

  Variable sa: StoreAtomicity reqFn respFn.

  Record State :=
    { mem: Addr -> Data;
      next: Addr -> Proc -> Index
    }.

  Inductive AtomicTrans s: State -> Set :=
  | AReq: forall a c, AtomicTrans s (Build_State
                                    (match desc (reqFn a c (next s a c)) with
                                       | Ld => mem s
                                       | St => fun a' =>
                                         if decAddr a a'
                                         then dataQ (reqFn a' c (next s a c))
                                         else mem s a'
                                     end)
                                    (fun a' t => 
                                       if decAddr a a'
                                       then
                                         match decProc t c with
                                                   | left _ => S (next s a' t)
                                                   | _ => next s a' t
                                         end
                                       else next s a' t
                                    ))
  | Idle: AtomicTrans s s.

  Inductive AtomicTrans': State -> State -> Set :=
  | AReq': forall s a c, AtomicTrans' s (Build_State
                                           (match desc (reqFn a c (next s a c)) with
                                              | Ld => mem s
                                              | St => fun a' =>
                                                        if decAddr a a'
                                                        then dataQ (reqFn a' c (next s a c))
                                                        else mem s a'
                                            end)
                                           (fun a' t =>
                                              if decAddr a a'
                                              then match decProc t c with
                                                     | left _ => S (next s a' t)
                                                     | _ => next s a' t
                                                   end
                                              else next s a' t
                                        ))
  | Idle': forall s, AtomicTrans' s s.

  Definition get' s s' (t: AtomicTrans s s') :=
    match t with
      | AReq a c => AReq' s a c
      | Idle => Idle' s
    end.

  Definition AtomicList := TransList AtomicTrans (Build_State initData (fun a t => 0)).

  Definition getTransNext n s (al: AtomicList n s) :=
    match respFn n with
      | Some r => Build_NextTrans _ _ _ (AReq s (addrR r) (procR r))
      | None => Build_NextTrans _ _ _ (Idle s)
    end.

  Lemma nextLe a t c: next (getTransSt getTransNext t) a c <=
                      next (getTransSt getTransNext (S t)) a c.
  Proof.
    pose (getTrans getTransNext t) as trans;
    unfold getTransSt;
    unfold getTransList;
    fold (getTransList getTransNext t); simpl.
    destruct trans; [simpl; destruct (decProc c c0); destruct (decAddr a0 a) | ]; omega.
  Qed.

  Lemma nextStarLe a t1 t2 c (cond: t1 <= t2): next (getTransSt getTransNext t1) a c <=
                                               next (getTransSt getTransNext t2) a c.
  Proof.
    remember (t2-t1) as td; assert (H: t2 = t1 + td) by omega;
    rewrite H in *; clear t2 cond H Heqtd.
    induction td.
    assert (H: t1 + 0 = t1) by omega; rewrite H; omega.
    assert (H: t1 + S td = S (t1 + td)) by omega; rewrite H; clear H;
    pose proof (nextLe a (t1 + td) c) as sth.
    omega.
  Qed.

  Lemma reqImpGt t: match getTrans getTransNext t with
                      | AReq a c => S (next (getTransSt getTransNext t) a c) =
                                 next (getTransSt getTransNext (S t)) a c /\
                                 forall a' c', (a' <> a \/ c' <> c) ->
                                            next (getTransSt getTransNext t ) a' c' =
                                            next (getTransSt getTransNext (S t)) a' c'
                      | Idle => forall a c, next (getTransSt getTransNext t ) a c =
                                            next (getTransSt getTransNext (S t)) a c
                    end.
  Proof.
    unfold getTransSt.
    unfold getTransList; fold (getTransList getTransNext t); simpl.
    destruct (getTrans getTransNext t).
    simpl.
    destruct (decProc c c); destruct (decAddr a a).
    constructor. omega.
    intros a' c' c'_neq.
    destruct (decProc c' c); destruct (decAddr a a').
    assert (a' = a) by auto; intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
    intuition.
  Qed.

  Theorem uniqAtomLabels:
    forall t1 t2,
      match getTrans getTransNext t1, getTrans getTransNext t2 with
        | AReq a1 c1, AReq a2 c2 =>
          a1 = a2 ->
          c1 = c2 ->
          next (getTransSt getTransNext t1) a1 c1 =
          next (getTransSt getTransNext t2) a2 c2 ->
          t1 = t2
        | _, _ => True
      end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros a_eq c_eq n_eq.
    rewrite <- c_eq, <- a_eq in *.
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.

    destruct sth1 as [u1 _];
      destruct sth2 as [u2 _].
    destruct opts as [eq | [lt | gt]].
    assumption.

    Ltac finish a c cond :=
      pose proof (nextStarLe a c cond) as use;
      assert False by omega; intuition.
    finish a c lt.
    finish a c gt.

    intuition.
    intuition.
  Qed.

  Theorem localAtomOrdering:
    forall t1 t2, match getTrans getTransNext t1, getTrans getTransNext t2 with
                    | AReq a1 c1, AReq a2 c2 =>
                      a1 = a2 ->
                      c1 = c2 ->
                      next (getTransSt getTransNext t1) a1 c1 <
                      next (getTransSt getTransNext t2) a2 c2 ->
                        t1 < t2
                    | _, _ => True
                  end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros a_eq c_eq n_lt.
    rewrite <- c_eq, <- a_eq in *.
    destruct sth1 as [u1 _]; destruct sth2 as [u2 _].
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct opts as [eq | [lt | gt]].
    rewrite eq in *; assert False by omega; intuition.
    intuition.
    pose proof (nextStarLe a c gt) as use;
      assert False by omega; intuition.

    intuition.
    intuition.
  Qed.

  Theorem allAtomPrev a t c i:
    next (getTransSt getTransNext t) a c > i ->
    exists t', t' < t /\ match getTrans getTransNext t' with
                           | AReq a' c' => a = a' /\ c = c' /\
                                       next (getTransSt getTransNext t') a' c' = i
                           | Idle => False
                         end.
  Proof.
    intros gt.
    induction t.
    simpl in gt.
    assert False by omega; intuition.
    pose proof (nextLe a t c) as sth.
    assert (opts: next (getTransSt getTransNext (S t)) a c =
                  next (getTransSt getTransNext t) a c \/
                  next (getTransSt getTransNext (S t)) a c >
                  next (getTransSt getTransNext t) a c) by (unfold Index; omega).
    destruct opts as [e|n].
    rewrite e in gt; destruct (IHt gt) as [t' [cond rest]]; exists t'; constructor;
    [ omega | intuition].
    assert (opts: next (getTransSt getTransNext t) a c = i \/
                  next (getTransSt getTransNext t) a c > i \/
                  next (getTransSt getTransNext t) a c < i) by (unfold Index; omega).
    destruct opts as [eq | [lt | gtt]].
    exists t; constructor.
    omega.
    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    destruct (decProc c c0).
    destruct (decAddr a a0).
    rewrite e, e0 in *; intuition.
    assert (H: a <> a0 \/ c <> c0) by intuition.
    specialize (u2 a c H).
    assert False by omega; intuition.
    assert (H: a <> a0 \/ c <> c0) by intuition.
    specialize (u2 a c H).
    assert False by omega; intuition.
    specialize (sth2 a c);
      assert False by omega; intuition.

    destruct (IHt lt) as [t' cond].
    exists t'; constructor; [omega | intuition].

    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    specialize (u2 a c).
    destruct (decAddr a a0).
    destruct (decProc c c0).
    rewrite <- e, <- e0 in *.
    assert False by omega; intuition.
    assert (H: a <> a0 \/ c <> c0) by intuition;
      rewrite e in *;
      specialize (u2 H); assert False by omega; intuition.
    assert (H: a <> a0 \/ c <> c0) by intuition;
      specialize (u2 H); assert False by omega; intuition.
    specialize (sth2 a c).
    assert False by omega; intuition.
  Qed.

  Definition noCurrAtomStore a t :=
    match getTrans getTransNext t with
      | AReq a' c' =>
        a = a' ->
        let (descQ', dtQ') :=
            reqFn a' c' (next (getTransSt getTransNext t) a' c') in
          descQ' = St -> False
      | _ => True
    end.

  Definition noAtomStore a tl t:=
    forall t', tl <= t' < t -> noCurrAtomStore a t'.

  Definition matchAtomStore a cm tm t :=
    let (descQm, dtQm) :=
        reqFn a cm (next (getTransSt getTransNext tm) a cm) in
    mem (getTransSt getTransNext t) a = dtQm /\
    descQm = St.

  Definition lastMatchAtomStore a tm t :=
    match getTrans getTransNext tm with
      | AReq am cm => a = am /\ matchAtomStore a cm tm t /\
                      noAtomStore a (S tm) t
      | _ => False
    end.

  Definition latestAtomValue a t :=
    (mem (getTransSt getTransNext t) a = initData a /\
     noAtomStore a 0 t) \/
    (exists tm,
       tm < t /\ lastMatchAtomStore a tm t).

  Definition atomNoPrevNonSt a t :=
    noAtomStore a 0 t /\
    mem (getTransSt getTransNext (S t)) a = initData a /\
    noCurrAtomStore a t.

  Definition atomPrevNonSt a t :=
    (exists tm,
       tm < t /\
       match getTrans getTransNext tm with
         | AReq am cm => a = am /\ matchAtomStore a cm tm (S t) /\
                     noAtomStore a (S tm) t
         | _ => False
       end) /\
    noCurrAtomStore a t.

  Definition atomSt a t :=
    lastMatchAtomStore a t (S t).

  Lemma latestAtomInd a t (now: atomNoPrevNonSt a t \/ atomPrevNonSt a t \/ atomSt a t):
    latestAtomValue a (S t).
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
    constructor.
    intuition.
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

  Lemma latestAtomValueHolds a t: latestAtomValue a t.
  Proof.
    induction t.

    Case "0".
    left; constructor; [| intros t' contra; assert False by omega]; intuition.

    Case "S t".
    apply latestAtomInd.

    unfold atomNoPrevNonSt.
    unfold atomPrevNonSt.

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

    SCase "AReq".
    destruct (decAddr a a0).
    rewrite <- e in *; clear e.

    SSCase "a = a0".
    case_eq (reqFn a c (next (lSt (getTransList getTransNext t)) a c)); simpl;
    intros desc dataQ reqF.
    destruct desc.

    SSSCase "Ld".
    simpl in *.
    destruct IHt.

    SSSSCase "NoPrev".
    left.
    intuition.
    discriminate.

    SSSSCase "Prev".
    right; left.
    intuition.
    discriminate.

    SSSCase "St".
    right; right.
    destruct (decAddr a a).
    constructor. intuition.
    constructor.
    constructor.
    rewrite reqF; simpl.
    intuition.
    intuition.
    intuition omega.

    intuition.

    simpl in *.
    destruct IHt.
    left.
    constructor.
    intuition.
    destruct (desc (reqFn a0 c (next (lSt (getTransList getTransNext t)) a0 c))).
    intuition.
    destruct (decAddr a0 a).
    assert False by auto.
    intuition.
    intuition.

    right.
    left.
    constructor.
    destruct (desc (reqFn a0 c (next (lSt (getTransList getTransNext t)) a0 c))).
    intuition.
    destruct (decAddr a0 a).
    assert False by auto.
    intuition.
    intuition.
    intuition.

    SSCase "Idle".
    destruct IHt; intuition.
  Qed.


  Theorem storeAtomicityAtom:
    forall t,
      match getTrans getTransNext t with
        | AReq a c =>
          let (descQ, dtQ) := reqFn a c (next (getTransSt getTransNext t) a c) in
          match descQ with
            | Ld => latestAtomValue a t
            | St => True 
          end
        | _ => True
      end.
  Proof.
    intros t.
    pose proof (fun a => latestAtomValueHolds a t).
    destruct (getTrans getTransNext t).
    destruct (reqFn a c (next (getTransSt getTransNext t) a c)) as [desc _].
    destruct desc.
    intuition.
    intuition.
    intuition.
  Qed.

  Definition atomicResp s s' (t: AtomicTrans s s') :=
    match t with
      | AReq a c => Some (Build_Resp a c (next s a c)
                                  match desc (reqFn a c (next s a c)) with
                                    | Ld => mem s a
                                    | St => initData zero
                                  end)
      | Idle => None
    end.

  Definition sameResp r1 r2 :=
    match r1, r2 with
      | Some (Build_Resp a1 p1 i1 d1), Some (Build_Resp a2 p2 i2 d2) =>
        a1 = a2 /\ p1 = p2 /\ i1 = i2 /\ d1 = d2
      | Some _, None => False
      | None, Some _ => False
      | None, None => True
    end.

  Theorem sameRespIsEq: forall r1 r2, sameResp r1 r2 <-> r1 = r2.
  Proof.
    intros r1 r2.
    constructor; unfold sameResp.
    intros.
    repeat destructAll.
    destruct H as [x [y [z w]]].
    rewrite x, y, z, w.
    reflexivity.

    intuition.
    intuition.
    intuition.
    intuition.
    rewrite H in *.
    repeat destructAll.
    intuition.
    intuition.
  Qed.

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

    Lemma addrSame:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp a1 c1 _ _), Some (Build_Resp a2 c2 _ _) => a1 = a2
        | _, _ => True
      end.
    Proof.
      assocResp.
      destruct (respFn t); simpl.
      destruct r; intuition.
      intuition.
    Qed.

    Lemma procSame:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp a1 c1 _ _), Some (Build_Resp a2 c2 _ _) => c1 = c2
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
        | Some (Build_Resp _ _ i1 _), Some (Build_Resp _ _ i2 _) => i1 > i2 -> False
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r caseR; destruct r; simpl in *.
      intros nextGt.
      pose proof (allAtomPrev _ _ _ nextGt) as [t' [t'_lt_t allPrev]].
      specialize (prevEq t'_lt_t).
      assocResp.
      case_eq (respFn t').
      intros r caseR'; destruct r; rewrite caseR' in *; simpl in *.
      pose proof (uniqRespLabels sa t t') as uniq.
      rewrite caseR, caseR' in uniq.
      destruct prevEq as [_ [_ [idEq _]]].
      rewrite <- idEq in allPrev.
      assert (tEq: t = t') by (generalize allPrev uniq; clear; intuition).
      assert False by omega; intuition.
      intros caseR'; rewrite caseR' in *; intuition.
      intros caseR; simpl in *; intuition.
    Qed.

    Lemma nextLtFalse:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ _ i1 _), Some (Build_Resp _ _ i2 _) => i1 < i2 -> False
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
      destruct prevEq as [_ [_ [idEq _]]].
      assert (tEq: t = t') by (generalize allPrev idEq uniq; clear;
                               unfold Index; intuition).
      assert False by omega; intuition.
      intros caseR'; rewrite caseR' in *; intuition.
      intros caseR; simpl in *; intuition.
    Qed.

    Lemma nextEq:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ _ i1 _), Some (Build_Resp _ _ i2 _) => i1 = i2
        | _, _ => True
      end.
    Proof.
      pose proof nextLtFalse;
      pose proof nextGtFalse;
      repeat destructAll; try (omega); unfold Index; intuition.
    Qed.

    Lemma loadMatch:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ _ _ d1), Some (Build_Resp _ _ _ d2) =>
          d1 = d2
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r respEq; destruct r; simpl in *.
      case_eq (desc (reqFn addrR procR (next (lSt (nextTransList t)) addrR procR))).
      intros isLd.
      pose proof nextEq as nextEq.
      pose proof (storeAtomicity sa t) as atom1.
      pose proof (storeAtomicityAtom t) as atom2.
      assocResp.
      rewrite respEq in *.
      simpl in *.
      rewrite nextEq in *.
      destruct (reqFn addrR procR idx).
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
      destruct prevEq as [_ [_ [idEq _]]].
      destruct stMatch as [u0 rest].
      rewrite <- idEq, u0 in *.
      rewrite <- idEq in rest.
      destruct (reqFn addrR0 procR0 idx0).
      destruct rest as [[u1 u2] _].
      
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
      destruct prevEq as [_ [_ [idEq _]]].
      rewrite <- idEq in *.
      destruct (reqFn addrR0 procR0 idx0).
      destruct stMatch as [u0 [u1 [u2 _]]].
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

      destruct stMatch2 as [u3 stMatch2].
      rewrite u3 in *.

      destruct prev1 as [_ [_ [i1Eq d1Eq]]].
      rewrite <- i1Eq in *;
      rewrite d1Eq in *; clear d1Eq.
      destruct prev2 as [_ [_ [i2Eq d2Eq]]].
      rewrite <- i2Eq in *;
      rewrite d2Eq in *; clear d2Eq.

      simpl in *.

      assert (opts: tm1 = tm2 \/ tm1 < tm2 \/ tm1 > tm2) by omega.
      destruct opts.

      SSCase "tm1 = tm2".
      rewrite H in *.
      rewrite r1Eq in r2Eq.
      injection r2Eq as dEq iEq pEq aEq.
      rewrite dEq in *;
        rewrite iEq in *;
        rewrite pEq, aEq in *.
      destruct (reqFn addrR0 procR0 idx0).
      destruct stMatch1 as [u0 [u1 _]].
      destruct stMatch2 as [[u2 _] _].
      rewrite <- u1 in u2;
        assumption.

      destruct H.

      SSCase "tm1 < tm2".
      destruct (reqFn addrR1 procR1 idx1).
      destruct stMatch1 as [u0 stMatch1].
      rewrite u0 in *.
      destruct stMatch1 as [_ [_ noLater]].
      assert (c1: tm1 < tm2 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r2Eq in noLater.
      destruct (reqFn addrR1 procR0 idx0).
      generalize stMatch2 noLater; clear; intuition.

      SSCase "tm2 < tm1".
      destruct (reqFn addrR0 procR0 idx0).
      destruct stMatch2 as [_ noLater].
      assert (c1: S tm2 <= tm1 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r1Eq in noLater.
      simpl in *.
      rewrite <- i1Eq in *.
      destruct (reqFn addrR1 procR1 idx1).
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
      destruct (reqFn addrR procR idx).
      simpl in *.
      rewrite r in *.
      auto.

      intros.
      repeat destructAll; intuition.
    Qed.

    Lemma allMatch:
      atomicResp (getTrans getTransNext t) = respFn t.
    Proof.
      pose proof addrSame.
      pose proof bothSomeOrNone.
      pose proof procSame.
      pose proof nextEq.
      pose proof loadMatch.

      repeat destructAll; intuition.
      rewrite H, H1, H2, H3 in *; reflexivity.
    Qed.
  End PrevMatch.



  Theorem obeysP: forall n,
                    respFn n = atomicResp (getTrans getTransNext n).
  Proof.
    apply strong_ind.
    intros t prevEq.
    assert (prevEq': forall ti, ti < t ->
                       sameResp (respFn ti) (atomicResp (getTrans getTransNext ti))).
    intros.
    specialize (prevEq ti H).
    pose proof (sameRespIsEq (respFn ti) (atomicResp (getTrans getTransNext ti))).
    intuition.
    
    pose proof (allMatch prevEq') as sth.
    unfold sameResp.
    repeat destructAll;
    repeat f_equal; intuition.
  Qed.

  Definition getAtomicResp n := atomicResp (getTrans getTransNext n).

  Lemma respEq n: respFn n = getAtomicResp n.
  Proof.
    apply (obeysP n).
  Qed.

  Definition justTrans n :=
    match getNSystem n with
      | exist (t, _) _ => t
    end.

  Lemma fullEq n:
    match getInfo (justTrans n), get' (getTrans getTransNext n) with
      | Some (a, p, d, w, ld), AReq' s a' p' =>
        a = a' /\ p = p' /\
        match w with
          | Ld => ld = (mem s) a
          | St => ld = initData zero
        end
      | None, Idle' s => True
      | _, _ => False
    end.
  Proof.
    unfold get'.
    unfold justTrans; simpl.
    pose proof (semiEq n) as semiEq.
    pose proof (semiEq' n) as semiEq'.
    pose proof (respEq n) as respEq.
    pose proof (respEq) as respEqExp.
    unfold getAtomicResp, atomicResp, respFn in respEqExp.
    unfold respFn in semiEq.
    destruct (getNSystem n) as [x y].
    destruct x as [t o].
    simpl in y.
    destruct (getInfo t) as [p|].
    destruct p as [p ld], p as [p w], p as [p _], p as [a p].
    destruct (getTrans getTransNext n) as [a' |].
    injection respEqExp; intros dEq idEq pEq aEq; clear respEqExp.
    destruct o as [i|].
    rewrite <- semiEq', aEq, pEq, <- idEq in *.
    destruct (desc (reqFn a' c i)); intuition.
    intuition.
    discriminate.
    destruct (getTrans getTransNext n) as [a' |].
    discriminate.
    intuition.
  Qed.

  Inductive FullTrans: (Rest * State) -> (Rest * State) -> Set :=
  | FTrans: forall r1 s1 r2 s2 (ts: System r1 r2) (ta: AtomicTrans' s1 s2),
              match getInfo ts, ta with
                | Some (a, p, d, w, ld), AReq' s a' p' =>
                  a = a' /\ p = p' /\
                  match w with
                    | Ld => ld = (mem s) a
                    | St => ld = initData zero
                  end
                | None, Idle' s => True
                | _, _ => False
              end -> FullTrans (r1, s1) (r2, s2).

  CoInductive FullStream: (Rest * State) -> Set :=
  | FCons: forall s s', FullTrans s s' -> FullStream s' -> FullStream s.

  
End ForAddr.
