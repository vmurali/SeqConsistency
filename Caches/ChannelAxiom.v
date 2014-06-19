Require Import Rules DataTypes Channel Omega Useful List Coq.Logic.Classical ChannelAxiomHelp.

Module mkChannel: Channel mkDataTypes.
  Import mkDataTypes.
  Section local.
    Context {s: ChannelType}.
    Context {p c: Cache}.

    Definition uniqMark1 {m n t}  := @ChannelAxiomHelp.uniqMark1 s p c m n t.

    Definition uniqMark2 {m n t}  := @ChannelAxiomHelp.uniqMark2 s p c m n t.

    Definition uniqSend1 {m n t} := @uniqMark1 m n t.

    Definition uniqSend2 {m t1 t2} := @uniqMark2 m t1 t2.

    Theorem uniqRecv1: forall {m n t}, recv s p c t m -> recv s p c t n -> m = n.
    Proof.
      intros m n t markm markn.
      unfold recv in *.
      destruct (trans oneBeh t).
      firstorder.
      firstorder.
      firstorder.

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

      firstorder.

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

      firstorder.

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
    Qed.

    Definition uniqProc1 {m n t} := @uniqRecv1 m n t.
    Definition uniqDeq1 {m n t} := @uniqRecv1 m n t.

    Theorem sendImpMark: forall {m t}, send s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t sendm.
      exists t.
      assert (H: t <= t) by omega.
      firstorder.
    Qed.

    Theorem procImpRecv: forall {m t}, proc s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Proof.
      intros m t procm.
      exists t.
      assert (H: t <= t) by omega.
      firstorder.
    Qed.

    Definition deqImpProc {m t} := @procImpRecv m t.


    Definition recvImpSend {m t} := @ChannelAxiomHelp.recvImpSend s p c m t.
    Definition uniqRecv2 {m : Mesg} {t1 t2: Time} := @ChannelAxiomHelp.uniqRecv2 s p c t1 t2 m.

    Definition uniqProc2 {m t1 t2} := @uniqRecv2 m t1 t2.
    Definition uniqDeq2 {m t1 t2} := @uniqRecv2 m t1 t2.

  End local.
End mkChannel.