Require Import Compatible DataTypes Rules Channel MsiState List Useful ChannelAxiomHelp.

Module mkCompatBehavior (ch: ChannelPerAddr mkDataTypes): CompatBehavior mkDataTypes ch.
  Import mkDataTypes ch.
  Section Node.
    Context {n: Cache}.
    Context {a: Addr}.
    Context {t: Time}.

    Theorem sendPCond: forall {p}, defined n -> defined p -> parent n p ->
                                   forall {m},
                                     mark mch n p a t m ->
                                     forall {c}, defined c -> parent c n ->
                                                 sle (dir n c a t) (to m).
    Proof.
      intros p defn defp n_p m markm c defc c_n.
      unfold dir in *; unfold mark in *; unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).
      firstorder.
      firstorder.
      destruct markm as [[_ [_ [use _]]] _]; discriminate.
      destruct markm as [[use1 [use2 _]] _];
      rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p1 n_p); firstorder.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
      rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p1 n_p); firstorder.

      assert (H: r = last (ch (sys oneBeh t) mch p0 c0) dmy) by auto.
      destruct markm as [[use2 [use3 [_ [_ [use4 [use5 _]]]]]] use1];
        rewrite use2 in *; rewrite use3 in *; rewrite <- H in *; rewrite <- use1 in *;
        rewrite use5 in *; rewrite use4 in *;
        specialize (s0 c defc c_n);
        assumption.

      firstorder.

      destruct markm as [[use2 [use3 [_ [_ [use4 [use5 _]]]]]] use1];
        rewrite use2 in *; rewrite use3 in *; rewrite <- use1 in *;
        rewrite use5 in *; rewrite use4 in *;
        specialize (s0 c defc c_n);
        assumption.

      firstorder.
    Qed.

    Theorem sendCCond: forall {c}, defined n -> defined c ->
                                   parent c n ->
                                   forall {m},
                                     mark mch n c a t m ->
                                     sle (to m) (state n a t) /\
                                     forall {c'},
                                       defined c' -> 
                                       c' <> c ->
                                       parent c' n ->
                                       sle (dir n c' a t)
                                           match to m with
                                             | Mo => MsiState.In
                                             | Sh => Sh
                                             | MsiState.In => Mo
                                           end.
    Proof.
      intros c defn defc c_n m markm.
      unfold dir in *.
      unfold state in *.
      unfold mark in *.
      unfold mkDataTypes.mark in *.
      destruct (trans oneBeh t).

      firstorder.
      firstorder.
      destruct markm as [[_ [_ [use _]]] _]; discriminate.

      destruct markm as [[use1 [use2 [_ [_ [use25 [use3 _]]]]]] use4];
      rewrite <- use1 in *; rewrite <- use2 in *; rewrite use4 in *; rewrite use3 in *;
      rewrite use25 in *; firstorder.

      firstorder.

      destruct markm as [[_ [_ [use _]]] _]; discriminate.

      destruct markm as [[use1 [use2 _]] _];
        rewrite <- use1 in *; rewrite <- use2 in *; pose proof (noCycle c_n p0); firstorder.
      firstorder.
      destruct markm as [[use1 [use2 _]] _];
        rewrite <- use1 in *; rewrite <- use2 in *; pose proof (noCycle c_n p0); firstorder.

      firstorder.
    Qed.

    Theorem oneRespC: forall {c1 c2}, defined n -> defined c1 -> defined c2 ->
                      parent c1 n -> parent c2 n ->
                      forall {m1}, (mark mch n c1 a t m1 \/ recv mch c1 n a t m1) ->
                                   forall {m2},
                                     (mark mch n c2 a t m2 \/ recv mch c2 n a t m2) -> c1 = c2.
    Proof.
      intros c1 c2 defn defc1 defc2 c1_n c2_n m1 sthm1 m2 sthm2.
      unfold mark in *.
      unfold mkDataTypes.mark in *.
      unfold recv in *; unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      firstorder.
      firstorder.
      destruct sthm1 as [[[_ [_ [use _]]] _] | easy]; [discriminate | firstorder].
      destruct sthm1 as [[[_ [use1 _]] _] | [[_ [_ [use1 _]]] _] ]; destruct sthm2 as [[[_ [use2 _]] _] | [[_ [_ [use2 _]]] _] ].
      rewrite use1 in use2; assumption.
      pose proof (enqC2P p0 n0) as k0.
      rewrite k0 in use2.
      discriminate.
      pose proof (enqC2P p0 n0) as k0.
      rewrite k0 in use1.
      discriminate.
      pose proof (enqC2P p0 n0) as k0.
      rewrite k0 in use1.
      discriminate.

      destruct sthm1 as [use1 | [[use1 [use2 _]] _] ];
      firstorder;
      rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p0 c1_n); firstorder.

      destruct sthm1 as [[[_ [_ [use _]]] _] | easy]; [discriminate | firstorder].
      

      destruct sthm1 as [[[use1 [use2 _]] _] | [[use1 [use2 _]] _]];
      rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p0 c1_n); firstorder.

      destruct sthm1 as [use1 | [[use2 _] _]].
      firstorder.
      destruct sthm2 as [use21 | [[use22 _] _]].
      firstorder.
      rewrite use2 in use22; assumption.
      
      destruct sthm1 as [[[use1 [use2 _]] _] | use];
      [rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p0 c1_n); firstorder
                                                                             | firstorder].

      destruct sthm1 as [ use | [[use1 [use2 _]] _]];
        [firstorder | rewrite use1 in *; rewrite use2 in *; pose proof (noCycle p0 c1_n);
                      firstorder].
    Qed.

    Theorem respPNoRespC: forall {p}, defined n -> defined p -> parent n p ->
                                    forall {m},
                                      (mark mch n p a t m \/ recv mch p n a t m) ->
                                      forall {c}, defined c -> parent c n -> forall mc,
                                        ~ (mark mch n c a t mc \/ recv mch c n a t mc).
    Proof.
      intros p defn defp n_p m sth1 c defc c_n mc sth2.
      unfold mark in*; unfold recv in *; unfold mkDataTypes.mark in *;
      unfold mkDataTypes.recv in *.
      destruct (trans oneBeh t).

      intuition.
      intuition.

      destruct sth1 as [[[_ [_ [use _]]] _] | easy]; [discriminate | firstorder].

      destruct sth1 as [[[u1 [u2 _]] _] | [[u1 [u2 _]] _]]; rewrite <- u1 in *;
                                         rewrite <- u2 in *; pose proof (noCycle p1 n_p);
                                         firstorder.

      destruct sth2 as [x | [[u1 [u2 _]] _]]; [intuition |
                                              rewrite <- u1 in *; rewrite <- u2 in *;
                                              pose proof (noCycle p1 c_n); intuition].

      destruct sth1 as [[[_ [_ [use _]]] _] | easy]; [discriminate | firstorder].

      destruct sth2 as [[[u1 [u2 _]] _] | [[u1 [u2 _]] _]]; rewrite <- u1 in *;
                                         rewrite <- u2 in *; pose proof (noCycle p1 c_n);
                                         firstorder.

      destruct sth1 as [x | [[u1 [u2 _]] _]]; [intuition |
                                              rewrite <- u1 in *; rewrite <- u2 in *;
                                              pose proof (noCycle p1 n_p); intuition].

      destruct sth2 as [[[u1 [u2 _]] _] | y]; [
                                              rewrite <- u1 in *; rewrite <- u2 in *;
                                              pose proof (noCycle p1 c_n); intuition |
        intuition].

      destruct sth2 as [x | [[u1 [u2 _]] _]]; [intuition|
                                              rewrite <- u1 in *; rewrite <- u2 in *;
                                              pose proof (noCycle p1 c_n); intuition].
    Qed.
  End Node.
  Theorem initCompat:
    forall {n c}, defined n -> defined c -> parent c n -> forall a, dir n c a 0 = MsiState.In.
  Proof.
    intros n c defn defc c_n a.
    unfold dir.
    pose proof (init oneBeh) as init.
    rewrite init.
    unfold initGlobalState.
    simpl; reflexivity.
  Qed.
End mkCompatBehavior.