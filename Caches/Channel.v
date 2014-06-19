Require Import DataTypes Omega.

Module Type Channel (dt: DataTypes).
  Import dt.

  Section local.
    Context {s: ChannelType}.
    Context {p c : Cache}.
    Axiom uniqMark1: forall {m n t}, mark s p c t m -> mark s p c t n -> m = n.
    Axiom uniqMark2: forall {m t1 t2}, mark s p c t1 m -> mark s p c t2 m -> t1 = t2.
    Axiom uniqSend1: forall {m n t}, send s p c t m -> send s p c t n -> m = n.
    Axiom uniqSend2: forall {m t1 t2}, send s p c t1 m -> send s p c t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c t m -> recv s p c t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c t1 m -> recv s p c t2 m -> t1 = t2.
    Axiom uniqProc1: forall {m n t}, proc s p c t m -> proc s p c t n -> m = n.
    Axiom uniqProc2: forall {m t1 t2}, proc s p c t1 m -> proc s p c t2 m -> t1 = t2.
    Axiom uniqDeq1: forall {m n t}, deq s p c t m -> deq s p c t n -> m = n.
    Axiom uniqDeq2: forall {m t1 t2}, deq s p c t1 m -> deq s p c t2 m -> t1 = t2.
    Axiom sendImpMark: forall {m t}, send s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Axiom recvImpSend: forall {m t}, recv s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Axiom procImpRecv: forall {m t}, proc s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Axiom deqImpProc: forall {m t}, deq s p c t m -> exists t', t' <= t /\ proc s p c t' m.
  End local.
End Channel.

Module mkChannelThms (dt: DataTypes) (ch: Channel dt).
  Import dt ch.
  Section local.
    Context {s: ChannelType}.
    Context {p c: Cache}.
    Theorem deqImpRecv: forall {m t}, deq s p c t m -> exists t', t' <= t /\ recv s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpProc deqm) as [t' [t'LeT procm]].
      pose proof (procImpRecv procm) as [t'' [t''LeT' recvm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem deqImpSend: forall {m t}, deq s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpRecv deqm) as [t' [t'LeT recvm]].
      pose proof (recvImpSend recvm) as [t'' [t''LeT' sendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem deqImpMark: forall {m t}, deq s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t deqm.
      pose proof (deqImpSend deqm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpSend: forall {m t}, proc s p c t m -> exists t', t' <= t /\ send s p c t' m.
    Proof.
      intros m t procm.
      pose proof (procImpRecv procm) as [t' [t'LeT recvm]].
      pose proof (recvImpSend recvm) as [t'' [t''LeT' sendm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpMark: forall {m t}, proc s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t procm.
      pose proof (procImpSend procm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem recvImpMark: forall {m t}, recv s p c t m -> exists t', t' <= t /\ mark s p c t' m.
    Proof.
      intros m t recvm.
      pose proof (recvImpSend recvm) as [t' [t'LeT sendm]].
      pose proof (sendImpMark sendm) as [t'' [t''LeT' markm]].
      assert (t''LeT: t'' <= t) by omega.
      firstorder.
    Qed.
    Theorem procImpMarkBefore: forall {m ts tr}, proc s p c tr m -> mark s p c ts m -> ts <= tr.
    Proof.
      intros m ts tr procm markm.
      pose proof (procImpMark procm) as [t' [t'_le_tr markm']].
      pose proof uniqMark2 markm markm' as ts_eq_t'.
      omega.
    Qed.
    Theorem recvImpMarkBefore: forall {m ts tr}, recv s p c tr m -> mark s p c ts m -> ts <= tr.
    Proof.
      intros m ts tr recvm markm.
      pose proof (recvImpMark recvm) as [t' [t'_le_tr markm']].
      pose proof uniqMark2 markm markm' as ts_eq_t'.
      omega.
    Qed.
  End local.
End mkChannelThms.

Module Type ChannelPerAddr (dt: DataTypes).

  Definition mark ch p c a t m := dt.mark ch p c t m /\ addr m = a.
  Definition send ch p c a t m := dt.send ch p c t m /\ addr m = a.
  Definition recv ch p c a t m := dt.recv ch p c t m /\ addr m = a.
  Definition proc ch p c a t m := dt.proc ch p c t m /\ addr m = a.
  Definition deq ch p c a t m := dt.deq ch p c t m /\ addr m = a.

  Section local.
    Context {s: ChannelType}.
    Context {p c : Cache} {a: Addr}.
    Axiom uniqMark1: forall {m n t}, mark s p c a t m -> mark s p c a t n -> m = n.
    Axiom uniqMark2: forall {m t1 t2}, mark s p c a t1 m -> mark s p c a t2 m -> t1 = t2.
    Axiom uniqSend1: forall {m n t}, send s p c a t m -> send s p c a t n -> m = n.
    Axiom uniqSend2: forall {m t1 t2}, send s p c a t1 m -> send s p c a t2 m -> t1 = t2.
    Axiom uniqRecv1: forall {m n t}, recv s p c a t m -> recv s p c a t n -> m = n.
    Axiom uniqRecv2: forall {m t1 t2}, recv s p c a t1 m -> recv s p c a t2 m -> t1 = t2.
    Axiom uniqProc1: forall {m n t}, proc s p c a t m -> proc s p c a t n -> m = n.
    Axiom uniqProc2: forall {m t1 t2}, proc s p c a t1 m -> proc s p c a t2 m -> t1 = t2.
    Axiom uniqDeq1: forall {m n t}, deq s p c a t m -> deq s p c a t n -> m = n.
    Axiom uniqDeq2: forall {m t1 t2}, deq s p c a t1 m -> deq s p c a t2 m -> t1 = t2.
    Axiom sendImpMark: forall {m t}, send s p c a t m -> exists t', t' <= t /\ mark s p c a t' m.
    Axiom recvImpSend: forall {m t}, recv s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom procImpRecv: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ recv s p c a t' m.
    Axiom deqImpProc: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ proc s p c a t' m.
    Axiom deqImpRecv: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ recv s p c a t' m.
    Axiom deqImpSend: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom deqImpMark: forall {m t}, deq s p c a t m -> exists t', t' <= t /\ mark s p c a t' m.
    Axiom procImpSend: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ send s p c a t' m.
    Axiom procImpMark: forall {m t}, proc s p c a t m -> exists t', t' <= t /\ mark s p c a t' m.
    Axiom recvImpMark: forall {m t}, recv s p c a t m -> exists t', t' <= t /\ mark s p c a t' m.
    Axiom procImpMarkBefore: forall {m ts tr}, proc s p c a tr m -> mark s p c a ts m ->
                                               ts <= tr.
    Axiom recvImpMarkBefore: forall {m ts tr}, recv s p c a tr m -> mark s p c a ts m ->
                                               ts <= tr.
  End local.
End ChannelPerAddr.

Module mkChannelPerAddr (dt: DataTypes) (ch: Channel dt) : ChannelPerAddr dt.
  Module chThm := mkChannelThms dt ch.
  Definition mark ch p c a t m := dt.mark ch p c t m /\ addr m = a.
  Definition send ch p c a t m := dt.send ch p c t m /\ addr m = a.
  Definition recv ch p c a t m := dt.recv ch p c t m /\ addr m = a.
  Definition proc ch p c a t m := dt.proc ch p c t m /\ addr m = a.
  Definition deq ch p c a t m := dt.deq ch p c t m /\ addr m = a.

  Set Implicit Arguments.
  Section local.
    Variable s: ChannelType.
    Variable p c : Cache.
    Variable a: Addr.
    Definition uniqMark1 {m n t} (sendm : mark s p c a t m) (sendn : mark s p c a t n) :=
      ch.uniqMark1 (proj1 sendm) (proj1 sendn).
    Definition uniqMark2 {m t1 t2} (sendm1: mark s p c a t1 m) (sendm2: mark s p c a t2 m) :=
      ch.uniqMark2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqSend1 {m n t} (sendm : send s p c a t m) (sendn : send s p c a t n) :=
      ch.uniqSend1 (proj1 sendm) (proj1 sendn).
    Definition uniqSend2 {m t1 t2} (sendm1: send s p c a t1 m) (sendm2: send s p c a t2 m) :=
      ch.uniqSend2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqRecv1 {m n t} (sendm : recv s p c a t m) (sendn : recv s p c a t n) :=
      ch.uniqRecv1 (proj1 sendm) (proj1 sendn).
    Definition uniqRecv2 {m t1 t2} (sendm1: recv s p c a t1 m) (sendm2: recv s p c a t2 m) :=
      ch.uniqRecv2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqProc1 {m n t} (sendm : proc s p c a t m) (sendn : proc s p c a t n) :=
      ch.uniqProc1 (proj1 sendm) (proj1 sendn).
    Definition uniqProc2 {m t1 t2} (sendm1: proc s p c a t1 m) (sendm2: proc s p c a t2 m) :=
      ch.uniqProc2 (proj1 sendm1) (proj1 sendm2).
    Definition uniqDeq1 {m n t} (deqm: deq s p c a t m) (deqn: deq s p c a t n) :=
      ch.uniqDeq1 (proj1 deqm) (proj1 deqn).
    Definition uniqDeq2 {m t1 t2} (deqm1: deq s p c a t1 m) (deqm2: deq s p c a t2 m) :=
      ch.uniqDeq2 (proj1 deqm1) (proj1 deqm2).

    Definition sendImpMark {m t} (deqm: send s p c a t m) :=
      match ch.sendImpMark (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ mark s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition recvImpSend {m t} (deqm: recv s p c a t m) :=
      match ch.recvImpSend (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpRecv {m t} (deqm: proc s p c a t m) :=
      match ch.procImpRecv (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ recv s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpProc {m t} (deqm: deq s p c a t m) :=
      match ch.deqImpProc (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ proc s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpRecv {m t} (deqm: deq s p c a t m) :=
      match chThm.deqImpRecv (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ recv s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpSend {m t} (deqm: deq s p c a t m) :=
      match chThm.deqImpSend (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition deqImpMark {m t} (deqm: deq s p c a t m) :=
      match chThm.deqImpMark (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ mark s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpSend {m t} (deqm: proc s p c a t m) :=
      match chThm.procImpSend (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ send s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition procImpMark {m t} (deqm: proc s p c a t m) :=
      match chThm.procImpMark (proj1 deqm) with
          | ex_intro x Px => 
              ex_intro (fun t' =>
                          t' <= t /\ mark s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.

    Definition recvImpMark {m t} (deqm: recv s p c a t m) :=
      match chThm.recvImpMark (proj1 deqm) with
          | ex_intro x Px =>
              ex_intro (fun t' =>
                          t' <= t /\ mark s p c a t' m) x (conj (proj1 Px) (conj (proj2 Px) (proj2 deqm)))
          end.
    Definition procImpMarkBefore: forall {m ts tr}, proc s p c a tr m -> mark s p c a ts m ->
                                               ts <= tr.
    Proof.
      intros m ts tr procm markm.
      unfold proc in *.
      unfold mark in *.
      destruct procm as [procm _].
      destruct markm as [markm _].
      apply (chThm.procImpMarkBefore procm markm).
    Qed.

    Definition recvImpMarkBefore: forall {m ts tr}, recv s p c a tr m -> mark s p c a ts m ->
                                                    ts <= tr.
    Proof.
      intros m ts tr procm markm.
      unfold proc in *.
      unfold mark in *.
      destruct procm as [procm _].
      destruct markm as [markm _].
      apply (chThm.recvImpMarkBefore procm markm).
    Qed.
  End local.
End mkChannelPerAddr.
