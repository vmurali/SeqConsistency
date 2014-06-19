Require Import DataTypes L1 StoreAtomicity LatestValue Cache Channel Compatible
Rules ChannelAxiom L1Axioms CompatBehavior LatestValueAxioms BehaviorAxioms MsiState.

Set Implicit Arguments.
Module mkTop.
  Module l1 := mkL1Axioms.
  Module ch' := mkChannel.
  Module ch := mkChannelPerAddr mkDataTypes ch'.
  Module comp := mkCompatBehavior ch.
  Module lv := mkLatestValueAxioms ch.
  Module ba := mkBehaviorAxioms.
  Module l1T := LatestValueTheorems mkDataTypes ch ba l1 comp lv.
    Import mkDataTypes l1 l1T.

    Definition respFn t :=
      match deqOrNot t with
        | inleft pf =>
          match pf with
            | exist (a, c,i) _ =>
              Some (Build_Resp a c i
                               match desc (reqFn a c i) with
                                 | Ld => data c a t
                                 | St => initData zero
                               end)
          end
        | inright _ => None
      end.

    Ltac finish := repeat match goal with
                            | [s: {_|_} |- _] => destruct s
                            | [x: (_ * _)%type |- _] => destruct x
                          end; simpl in *.

    Theorem uniqRespLabels':
      forall {t1 t2}, match respFn t1, respFn t2 with
                        | Some (Build_Resp a1 c1 i1 _), Some (Build_Resp a2 c2 i2 _) =>
                          a1 = a2 -> c1 = c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end.
    Proof.
      intros t1 t2; unfold respFn;
      destruct (deqOrNot t1); destruct (deqOrNot t2);
      solve [finish; intros H H0 H1; rewrite <- H, <- H1 in *; rewrite <- H0 in *;
             apply (uniqDeqProc2 d0 d) |
             finish; intuition | 
             intuition].
    Qed.

    Theorem localOrdering':
      forall {t1 t2}, match respFn t1, respFn t2 with
                        | Some (Build_Resp a1 c1 i1 _), Some (Build_Resp a2 c2 i2 _) =>
                          a1 = a2 -> c1 = c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end.
    Proof.
      intros t1 t2; unfold respFn;
      destruct (deqOrNot t1); destruct (deqOrNot t2).
      finish.
      intros H H0 H1.
      rewrite H, H0 in *.
      pose proof (deqOrder d d0 H1).
      unfold Time in *.
      assert (opts: t1 = t2 \/ t1 > t2) by omega.
      destruct opts as [e1 | e2].
      rewrite e1 in *.
      pose proof (uniqDeqProc d d0); omega.
      assumption.
      finish.
      intuition.
      intuition.
      intuition.
    Qed.

    Theorem allPrevious':
      forall {t2}, match respFn t2 with
                     | Some (Build_Resp a2 c2 i2 _) =>
                       forall {i1}, i1 < i2 -> exists t1, t1 < t2 /\
                                                          match respFn t1 with
                                                            | Some (Build_Resp a1 c1 i _) =>
                                                              a1 = a2 /\ c1 = c2 /\ i = i1
                                                            | None => False
                                                          end
                     | _ => True
                   end.
    Proof.
      intros t2; unfold respFn.
      destruct (deqOrNot t2).
      finish.
      intros i1 cond.
      pose proof (deqImpDeqBefore d cond) as [t' [cond2 deq2]].
      exists t'.
      destruct (deqOrNot t').
      finish.
      constructor.
      intuition.
      apply (uniqDeqProc3 d0 deq2).
      constructor.
      intuition.
      apply (n _ _ _ deq2).
      intuition.
    Qed.

    Theorem storeAtomicity':
        forall t,
          match respFn t with
            | Some (Build_Resp a c i d) =>
              let (descQ, dtQ) := reqFn a c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore reqFn respFn a t') \/
                  (exists tm,
                     tm < t /\
                     match respFn tm with
                       | Some (Build_Resp am cm im dm) =>
                         let (descQm, dtQm) := reqFn am cm im in
                         a = am /\ d = dtQm /\ descQm = St /\
                         forall t', tm < t' < t -> noStore reqFn respFn a t'
                       | _ => False
                     end)
                | St => d = initData zero 
              end
            | _ => True
          end.
    Proof.
      intros t.
      unfold respFn.
      unfold noStore.
      destruct (deqOrNot t).
      finish.
      pose proof (processDeq d) as procD.
      destruct (reqFn a c i); simpl.
      simpl in *.
      destruct desc.
      pose proof (deqLeaf d) as lf.
      pose proof (deqDef d) as def.
      assert (le: sle Sh (state c a t)) by
          (unfold sle; destruct (state c a t); auto).
      pose proof (latestValue def lf le) as lv.
      destruct lv as [[dtMatch noPrev]|prev].
      left.
      constructor; intuition.
      destruct (deqOrNot t').
      finish.
      pose proof (deqDef d0) as def0.
      assert (cond: 0 <= t' < t) by omega.
      specialize (noPrev _ cond _ i0 def0).
      destruct (reqFn a c0 i0).
      intros; simpl in *.
      rewrite H0 in *.
      intuition.
      intuition.
      right.
      destruct prev as [cb [ib [tb [defcb [tb_lt_t [deq_tb [isSt [dtM rest]]]]]]]].
      exists tb.
      constructor.
      intuition.
      destruct (deqOrNot tb).
      finish.
      pose proof (uniqDeqProc3 deq_tb d0) as [aeq [ceq ieq]].
      rewrite <- ceq in *; rewrite <- ieq, <- aeq in *.
      destruct (reqFn a cb ib); simpl in *.
      constructor. intuition.
      constructor. intuition.
      constructor. intuition.
      intros t' cond.
      destruct (deqOrNot t').
      finish.
      intros x.
      rewrite x in *.
      pose proof (deqDef d1) as defdeq.
      specialize (rest _ cond _ i1 defdeq).
      destruct (reqFn a c1 i1); simpl in *.
      generalize rest d1; clear; intuition.

      intuition.

      apply (n _ _ _ deq_tb).
      intuition.
      intuition.
    Qed.

    About StoreAtomicity.


    Theorem sa: StoreAtomicity reqFn respFn.
    Proof.
      apply (Build_StoreAtomicity reqFn respFn
            (@uniqRespLabels') (@localOrdering') (@allPrevious') (storeAtomicity')).
    Qed.
End mkTop.
