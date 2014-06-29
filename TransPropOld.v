Require Import List Coq.Logic.FunctionalExtensionality Omega.

Set Implicit Arguments.

Section Clos.
  Variable S L: Set.
  Variable A: S -> S -> option L -> Prop.
  Inductive Clos: S -> S -> list L -> Prop :=
  | Refl s: Clos s s nil
  | Trans a b ls c alpha: Clos a b ls -> A b c alpha ->
                          Clos a c match alpha with
                                     | Some x => x :: ls
                                     | None => ls
                                   end.

  Theorem singleTrans a b l: A a b (Some l) -> Clos a b (l::nil).
  Proof.
    intros H.
    apply (Trans (Refl a) H).
  Qed.

  Variable a: S.

  Record TransRec a a'' l ls :=
    { a': S;
      closa': Clos a a' ls;
      closa'': Clos a' a'' (l::nil)
    }.
  Theorem moreTrans:
    forall a'' l ls, Clos a a'' (l::ls) ->
                     exists a', Clos a a' ls /\ Clos a' a'' (l::nil).
  Proof.
    intros.
    remember (l::ls) as hell.
    induction H.
    discriminate.
    destruct alpha.
    injection Heqhell; intros.
    rewrite H1, H2 in *.
    pose proof (singleTrans H0) as sth.
    exists b; intuition.

    specialize (IHClos Heqhell); rewrite Heqhell in *; clear Heqhell; simpl in *.
    destruct IHClos as [a' [closa' closa'']].
    exists a'; intuition.
    apply (Trans closa'' H0).
  Qed.
End Clos.

Section Trans.
  Variable Sa Sb L: Set.
  Variable f: L -> option L.

  Variable A: Sa -> Sa -> option L -> Prop.
  Variable B: Sb -> Sb -> option L -> Prop.

  Variable sa: Sa.
  Variable sb: Sb.

  Fixpoint mapRm ls :=
    match ls with
      | l :: xs => match f l with
                     | Some x => x :: mapRm xs
                     | None => mapRm xs
                   end
      | nil => nil
    end.

  Variable sim: forall sa' ls, Clos A sa sa' ls ->
                               exists sb', Clos B sb sb' (mapRm ls).
  Theorem oneStep:
    forall sa' ls (closa': Clos A sa sa' ls) sa'' l,
      A sa' sa'' l ->
      exists sb', Clos B sb sb' (mapRm ls) /\
        exists sb'', Clos B sb' sb'' (match l with
                                        | None => nil
                                        | Some x => match f x with
                                                      | Some y => y :: nil
                                                      | None => nil
                                                    end
                                      end).
  Proof.
    intros.
    simpl in *.

    pose proof (Trans sa'' l closa'0 H) as trans.
    destruct (sim trans) as [sb'' closb''].

    destruct l.
    simpl in *.

    destruct (f l).
    pose proof (moreTrans closb'') as [sb' [closb' clos_b'']].

    exists sb'; intuition.
    exists sb''; intuition.

    exists sb''; intuition.
    exists sb''; constructor.

    exists sb''; intuition.
    exists sb''; constructor.
  Qed.
End Trans.


Section MultiTrans.
  Variable Sa L Idx: Set.
  Variable decIdx: forall i i': Idx, {i=i'}+{i<>i'}.
  Variable A: Idx -> Sa -> Sa -> option L -> Prop.

  Inductive Multi: (Idx -> Sa) -> (Idx -> Sa) -> option (Idx * L) -> Prop :=
  | Step m i x' l: A i (m i) x' l -> Multi m (fun i' =>
                                                if decIdx i i'
                                                then x'
                                                else m i') match l with
                                                             | None => None
                                                             | Some y => Some (i, y)
                                                           end.

  Variable sa: Idx -> Sa.

  Fixpoint filterId i (ls: list (Idx * L)) :=
    match ls with
      | nil => nil
      | (i', y) :: xs => if decIdx i i'
                         then y :: filterId i xs
                         else filterId i xs
    end.

  Theorem existsTrans: forall sa' ls,
                         Clos Multi sa sa' ls ->
                         forall i, Clos (A i) (sa i) (sa' i)
                                        (filterId i ls).
  Proof.
    intros sa' ls H.
    induction H.
    intros i.
    constructor.

    intros.
    specialize (IHClos i).
    destruct H0.
    destruct (decIdx i0 i).

    rewrite e in *; clear e.

    pose proof (Trans _ _ IHClos H0) as trans.

    destruct l.
    simpl.
    destruct (decIdx i i); intuition.

    intuition.

    destruct l.
    simpl.
    destruct (decIdx i i0).
    assert False by auto; intuition.
    intuition.
    intuition.
  Qed.

  Theorem constTrans: forall sa' ls i ls' sa'',
                        Clos Multi sa sa' ls ->
                        Clos (A i) (sa' i) sa'' ls' ->
                        Clos Multi sa (fun i' =>
                                         if decIdx i i'
                                         then sa''
                                         else sa' i') (map (fun x => (i, x)) ls' ++ ls).
  Proof.
    intros.
    remember (sa' i) as sth.
    induction H0.
    rewrite Heqsth in *.

    assert (sth: (fun i' => (if decIdx i i' then sa' i else sa' i')) = sa').
    apply (functional_extensionality).
    intros.
    destruct (decIdx i x).
    rewrite e in *; reflexivity.
    reflexivity.

    rewrite sth.
    intuition.

    specialize (IHClos Heqsth).

    pose proof (@Step (fun i' => if decIdx i i' then b else sa' i') i) as sth.

    simpl in sth.
    destruct (decIdx i i); simpl in *.

    specialize (sth _ _ H1).
    pose proof (Trans _ _ IHClos sth) as use1.

    assert (abc: (fun i' =>
               if decIdx i i' then c else if decIdx i i' then b else sa' i') =
            fun i' =>
              if decIdx i i' then c else sa' i').
    apply (functional_extensionality).
    intros.
    destruct (decIdx i x); reflexivity.
    rewrite abc in *.

    destruct alpha.

    assert (rew:(i, l):: map (fun x => (i,x)) ls0 ++ ls = map (fun x => (i, x)) (l::ls0)++ls) by
    reflexivity.

    rewrite rew in *.
    intuition.

    intuition.
    intuition.
  Qed.

  Theorem replaceMulti: forall sa' ls,
                          Clos Multi sa sa' ls ->
                          forall si' i,
                            Clos (A i) (sa i) si' (filterId i ls) ->
                            Clos Multi sa (fun i' => if decIdx i i'
                                                     then si'
                                                     else sa' i') ls.
  Proof.
    intros sa' ls H.
    remember sa as sth.
    induction H.

    intros.
    
    rewrite Heqsth in *.
    simpl in *.
    apply (constTrans (Refl Multi sa) H).

    intros.
    specialize (IHClos Heqsth).
    rewrite Heqsth in *.

    remember (sa i) as sth2.
    remember (filterId i match alpha with
                           | Some x => x :: ls
                           | None => ls
                         end) as sth3.

    rewrite Heqsth2, Heqsth3 in *.

    destruct H0.
    destruct l.

    simpl in *.
    destruct (decIdx i i0); simpl in *.
    rewrite <- e in *.

    discriminate.

    specialize (IHClos (sa i) i).
    rewrite <- Heqsth3 in *.

    specialize (IHClos (Refl (A i) (sa i))).

    assert ((fun i' : Idx => if decIdx i i' then sa i else m i') i0 = m i0).
    destruct (decIdx i i0); intuition.

    rewrite <- H1 in H0.
    pose proof (Step (fun i' : Idx => if decIdx i i' then sa i else m i') H0) as step.
    simpl in *.

    assert ((fun i' : Idx =>
            if decIdx i0 i' then x' else if decIdx i i' then sa i else m i') =
             (fun i' : Idx =>
                if decIdx i i' then sa i else if decIdx i0 i' then x' else m i')).
    apply (functional_extensionality).
    intros.
    destruct (decIdx i0 x), (decIdx i x).
    rewrite e, e0 in *.
    intuition.
    intuition.
    intuition.
    intuition.

    rewrite H2 in step.
    apply (Trans _ _ IHClos step).

    specialize (IHClos (sa i) i).
    rewrite <- Heqsth3 in *.
    specialize (IHClos (Refl (A i) (sa i))).

    destruct (decIdx i i0).
    rewrite <- e in *.

    assert ( (fun i' : Idx =>
      if decIdx i i' then sa i else if decIdx i i' then x' else m i') =
              (fun i' : Idx => if decIdx i i' then sa i else m i')).
    apply functional_extensionality.
    intros.
    destruct (decIdx i x); reflexivity.
    rewrite H1 in *.

    intuition.

    assert ((fun i' => if decIdx i i' then sa i else m i') i0 = m i0).
    destruct (decIdx i i0); intuition.

    rewrite <- H1 in H0.

    pose proof (Step (fun i' : Idx => if decIdx i i' then sa i else m i') H0) as step.
    simpl in *.

    pose proof (Trans _ _ IHClos step).

    assert ((fun i' : Idx =>
            if decIdx i0 i' then x' else if decIdx i i' then sa i else m i') =
             (fun i' : Idx =>
                if decIdx i i' then sa i else if decIdx i0 i' then x' else m i')).
    apply (functional_extensionality).
    intros.
    destruct (decIdx i0 x), (decIdx i x).
    rewrite e, e0 in *.
    intuition.
    intuition.
    intuition.
    intuition.

    rewrite H3 in H2.
    intuition.

    
    intuition.
    simpl in *.


    pose proof (Step 
    


    apply Trans; intuition.
    rewrite e in *.
    destruct (decIdx i x).
    rewrite e, e0 in *.

    

    destruct H0.
    pose proof 

    destruct in *.
    destruct alpha.
    simpl in *.
    destruct H0.
    simpl in *.
    destruct H0.

    destruct l; simpl in *.

    destruct (decIdx i i0).

    rewrite <- e in *.
    
    simpl in *.

    destruct alpha.


    simpl in *.
    destruct p.
    destruct (decIdx i i0).
    rewrite <- e in *.

    pose proof (moreTrans H1) as [a' [c1 c2]].
    specialize (IHClos a' i c1).

    assert ((fun i' => if decIdx i i' then a' else b i') i = a') by
        (destruct (decIdx i i); intuition).

    rewrite <- H2 in c2.

    destruct H0.
    dependent destruction H0.

    
    pose proof (constTrans (Trans _ _ IHClos H0) c2) as good.

    simpl in good.

    assert ((fun i' => if decIdx i i' then si' else if decIdx i i' then a' else b i') =
            fun i' => if decIdx i i' then si' else b i').
    apply functional_extensionality.
    intros.
    destruct (decIdx i x); reflexivity.

    rewrite H3 in *.

    intuition.

    specialize (IHClos _ _ H1).

    rewrite Heqsth in *.

    pose proof (Trans _ _ IHClos H0).
    constructor 2.

    destruct alpha.
    simpl in *.

    destruct p.
    destruct (decIdx i i0).
    
    constructor 2.



End MultiTrans.

Section Test.
  Variable Sa Sb L Idx: Set.
  Variable f: L -> option L.

  Variable decIdx: forall i i': Idx, {i=i'}+{i<>i'}.

  Variable A: Idx -> Sa -> Sa -> option L -> Prop.
  Variable B: Idx -> Sb -> Sb -> option L -> Prop.

  Variable sa: Idx -> Sa.
  Variable sb: Idx -> Sb.

  Definition An := Multi decIdx A.
  Definition Bn := Multi decIdx B.

  Variable sim: forall i sa' ls, Clos (A i) (sa i) sa' ls ->
                                 exists sb', Clos (B i) (sb i) sb' (mapRm f ls).

  Definition fMulti (l: (Idx * L)) :=
    match l with
      | (i, x) => match f x with
                    | None => None
                    | Some y => Some (i, y)
                  end
    end.

  Theorem multiSim: forall sa' ls, Clos An sa sa' ls ->
                                   exists sb', Clos Bn sb sb' (mapRm fMulti ls).
  Proof.
    intros.
    induction H.
    exists sb; constructor.

    destruct (IHClos sim) as [sb' closb'].

    destruct H0 as [sa' i a' l stepA].

    pose proof (existsTrans H i) as closai'.

    pose proof (oneStep f (@sim i) closai' _ _ stepA) as [sbi' [closb [sbi'' stepB]]].

    destruct l; simpl in *.

    destruct (f l); simpl in *.

    admit.

    exists sb'; intuition.
    exists sb'; intuition.
  Qed.

End Test.
