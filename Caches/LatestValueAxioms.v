Require Import Rules Channel DataTypes MsiState ChannelAxiomHelp.

Module mkLatestValueAxioms (ch: ChannelPerAddr mkDataTypes).
  Import mkDataTypes ch.

  Theorem toChild: forall {n a t p m},
                     defined n -> defined p ->
                     parent n p -> 
                     mark mch p n a t m -> from m = MsiState.In -> dataM m = data p a t.
  Proof.
    intros n a t p m defn defp n_p markm fromm.
    unfold mark in *; unfold data in *. unfold mkDataTypes.mark in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use3 [use0 _]] _];
    rewrite use3 in *; rewrite use0 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
    destruct markm as [[use3 [use0 _]] _];
    rewrite use3 in *; rewrite use0 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
  Qed.

  Theorem fromParent: forall {n a t p m}, defined n -> defined p ->
                      parent n p -> 
                      recv mch p n a t m -> from m = MsiState.In -> data n a (S t) = dataM m.
  Proof.
    intros n a t p m defn defp n_p recvm fromm.
    unfold recv in *; unfold data; unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    firstorder.
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle n_p p1); firstorder.
    simpl;
    assert (eq: m0 = List.last (ch (sys oneBeh t) mch p0 c) dmy) by auto;
      assert (eq2: a0 = addrB m0) by auto;
    destruct recvm as [[use1 [use2 [_ [use3 [_ [use4 [use5 _]]]]]]] use0]; rewrite <- eq in *;
    rewrite use1 in *; rewrite use2 in *;
    rewrite use3 in *; rewrite use4 in *; rewrite use0 in *; rewrite eq2 in *; rewrite fromm in *; rewrite use5 in *;
    destruct (decTree n n); destruct (decAddr a a); firstorder.
    firstorder.
    assert (e2: r = List.last (ch (sys oneBeh t) mch p0 c) dmy) by auto.
    rewrite <- e2 in recvm.
    rewrite e in *.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate. 
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle n_p p1); firstorder.
    firstorder.
    assert (e2: r = List.last (ch (sys oneBeh t) mch p0 c) dmy) by auto.
    rewrite <- e2 in recvm.
    rewrite e in *.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate. 
  Qed.

  Theorem toParent: forall {n a t c m},
                      defined n -> defined c ->
                      parent c n ->
                      mark mch c n a t m -> slt Sh (from m) -> dataM m = data c a t.
  Proof.
    intros n a t c m defn defc c_n markm isM.
    assert (fromm: from m = Mo) by (unfold slt; destruct (from m); firstorder); clear isM.
    unfold mark in *; unfold data in *. unfold mkDataTypes.mark in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[_ [_ [use _]]] _]; discriminate.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
    destruct markm as [[use0 [_ [_ [_ [_ [use1 [use2 _]]]]]]] use3];
    rewrite <- use1 in *; rewrite use3 in *; rewrite use0 in *; assumption.
    firstorder.
  Qed.

  Theorem fromChild: forall {n a t c m},
                       defined n -> defined c ->
                       parent c n ->
                       recv mch c n a t m -> slt Sh (from m) -> data n a (S t) = dataM m.
  Proof.
    intros n a t c m defn defc c_n recvm isM.
    assert (fromm: from m = Mo) by (unfold slt; destruct (from m); firstorder); clear isM.
    unfold recv in *; unfold data in *. unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).
    firstorder.
    firstorder.
    firstorder.
    pose proof (enqC2P p0 n0) as contra.
    rewrite contra in recvm.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
    destruct recvm as [[use1 [use2 _]] _];
    rewrite use1 in *; rewrite use2 in *; pose proof (noCycle c_n p0); firstorder.
    firstorder.
    assert (re: r = List.last (ch (sys oneBeh t) mch p c0) dmy) by auto.
    rewrite re in e.
    rewrite e in recvm.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
    simpl;
    assert (eq: m0 = List.last (ch (sys oneBeh t) mch c0 p) dmy) by auto;
      assert (eq2: a0 = addrB m0) by auto;
    destruct recvm as [[use1 [use2 [_ [use3 [_ [use4 [use5 _]]]]]]] use0]; rewrite <- eq in *;
    rewrite use1 in *; rewrite use2 in *;
    rewrite use3 in *; rewrite use4 in *; rewrite use0 in *; rewrite eq2 in *; rewrite fromm in *; rewrite use5 in *;
    destruct (decTree n n); destruct (decAddr a a); firstorder.
    firstorder.
    assert (re: r = List.last (ch (sys oneBeh t) mch p c0) dmy) by auto.
    rewrite re in e.
    rewrite e in recvm.
    destruct recvm as [[_ [_ [use _]]] _]; discriminate.
  Qed.

  Theorem initLatest: forall a, data hier a 0 = initData a /\ state hier a 0 = Mo.
  Proof.
    intros a.
    unfold data; unfold state.
    pose proof (init oneBeh) as initi.
    rewrite initi.
    unfold initGlobalState.
    simpl.
    destruct (decTree hier hier) as [eq |neq].
    constructor; firstorder.
    firstorder.
  Qed.

  Theorem deqImpData: forall {a n t i}, defined n -> deqR a n i t -> desc (reqFn a n i) = St ->
                                          data n a (S t) = dataQ (reqFn a n i).
  Proof.
    intros a n t i defn deqr isSt.
    unfold deqR in *; unfold data.
    destruct (trans oneBeh t).
    destruct deqr as [e1 [eq reqI]].
    rewrite <- e1, eq in *.
    rewrite reqI in e.
    rewrite e in isSt.
    discriminate.
    simpl.
    destruct deqr as [e1 [seq reqi]].
    destruct (decTree n c) as [eq | neq].
    rewrite e1, seq in *.
    rewrite reqi in *.
    destruct (decAddr a a).
    reflexivity.
    firstorder.
    assert (n = c) by auto; firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
  Qed.

  Theorem changeData:
    forall {n a t}, defined n ->
                    data n a (S t) <> data n a t ->
                    (exists m, (exists p, defined p /\ parent n p /\ recv mch p n a t m /\ from m = MsiState.In) \/
                               (exists c, defined c /\ parent c n /\ recv mch c n a t m /\
                                          slt Sh (from m))) \/
                    exists i, deqR a n i t /\ desc (reqFn a n i) = St.
  Proof.
    intros n a t defn dtNeq.
    unfold data in *; unfold recv in *; unfold deqR in *; unfold mkDataTypes.recv in *.
    destruct (trans oneBeh t).

    simpl in *. firstorder.

    simpl in *.
    right.
    destruct (decTree n c).
    destruct (decAddr a a0).
    rewrite e1, e2 in *.
    exists (req (sys oneBeh t) a c).
    firstorder; auto.
    rewrite e2 in *.
    firstorder.
    rewrite e2 in *.
    firstorder.

    simpl in *.
    firstorder.

    simpl in *.
    firstorder.

    simpl in *.
    firstorder.

    simpl in *.
    firstorder.

    simpl in *.
    left.
    exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m) (List.last (labelCh t mch p c) 0)).
    simpl.
    left.
    exists p.
    assert (sth: m = List.last (ch (sys oneBeh t) mch p c) dmy) by auto.
    rewrite <- sth in *.
    destruct (decTree n c) as [nEq | nNeq].
    rewrite <- nEq in *.
    destruct (decAddr a a0) as [aEq | aNeq].
    destruct (fromB m); intuition.
    firstorder.
    firstorder.

    simpl in *; firstorder.
    simpl in *; firstorder.

    simpl in *.
    left.
    exists (Build_Mesg (fromB m) (toB m) (addrB m) (dataBM m) (List.last (labelCh t mch c p) 0)).
    simpl.
    right.
    exists c.
    assert (sth: m = List.last (ch (sys oneBeh t) mch c p) dmy) by auto.
    rewrite <- sth in *.
    destruct (decTree n p) as [nEq | nNeq].
    rewrite <- nEq in *.
    destruct (decAddr a a0) as [aEq | aNeq].
    pose proof (enqC2P p0 n0) as sth2.
    rewrite <- sth in sth2.
    rewrite sth2.
    destruct (fromB m); intuition.
    firstorder.
    firstorder.

    simpl in *; firstorder.
    simpl in *; firstorder.
  Qed.

  Theorem deqImpNoSend: forall {c a i t},
                          defined c -> deqR a c i t ->
                          forall {m p}, defined p -> ~ mark mch c p a t m.
  Proof.
    unfold not; intros c a i t defc deqr m p defp markm.
    unfold deqR in *; unfold mark in *; unfold mkDataTypes.mark in *.

    destruct (trans oneBeh t); firstorder.
  Qed.
End mkLatestValueAxioms.
