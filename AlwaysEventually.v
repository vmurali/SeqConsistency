Set Implicit Arguments.

Section AlwaysEventually.
  Variable State: Set.
  Variable Trans: State -> State -> Set.

  CoInductive TransStream: State -> Set :=
  | TCons: forall s s' (t: Trans s s'), TransStream s' -> TransStream s.

  Variable P: forall s s', Trans s s' -> Prop.
  Variable P_dec: forall s s' (ts: Trans s s'), {P ts} + {~ P ts}.

  Inductive Eventually: forall s, TransStream s -> Type :=
  | Later: forall s s' (t: Trans s s') ts, Eventually ts -> Eventually (TCons t ts)
  | Now: forall s s' (t: Trans s s') ts, P t -> Eventually (TCons t ts).

  CoInductive AlwaysEventually: forall s, TransStream s -> Type :=
  | Final: forall s s' (t: Trans s s') ts, Eventually (TCons t ts) ->
                                           AlwaysEventually ts ->
                                           AlwaysEventually (TCons t ts).

  Require JMeq.

  Program Fixpoint getFirstTransState s (ts: TransStream s)
          (es: Eventually ts) (als: AlwaysEventually ts) :=
    match ts with
      | TCons s s' t ts' =>
        if P_dec t
        then (s, s')
        else @getFirstTransState s' ts' _ _
    end.

  Next Obligation.
    intros.
    destruct  als.
    Set Printing All.
    simpl.
    destruct es.
    destruct e.
    rewrite <- Heq_s in *.
  Program Fixpoint getFirst s (ts: TransStream s) (es: Eventually ts) (als: AlwaysEventually ts):  :=
    match ts with
      | TCons _ _ t ts' =>
        if P_dec t
        then ts
        else getFirst _ _
    end.
           
  Fixpoint getFirst 
  Record NextStream :=
    { ft: A;
      sn: B;
      stm: Stream;
      pf: P ft;
      alsThing: AlwaysEventually stm
    }.

  Definition injectionCons1 (x: A) ls' x0 s' (eq: Cons x ls' = Cons x0 s'):
    x = x0.
  Proof.
    injection eq; intros; assumption.
  Qed.

  Definition injectionCons2 (x: A) ls' x0 s' (eq: Cons x ls' = Cons x0 s'):
    ls' = s'.
  Proof.
    injection eq; intros; assumption.
  Qed.

  Fixpoint getFirst f ls (es: Eventually ls) (als: AlwaysEventually ls) {struct es}: NextStream :=
    match ls as ls0 return ls0 = ls -> NextStream with
      | Cons x ls' =>
        fun heq: Cons x ls' = ls =>
          match P_dec x with
            | left pp => Build_NextStream (f x pp)
                           pp
                           (match als in AlwaysEventually ls0
                                  return
                                  Cons x ls' = ls0 -> AlwaysEventually ls' with
                              | AE_n x0 s' _ als' =>
                                fun heq => eq_rect_r _ als' (injectionCons2 heq)
                            end heq)
            | right pp => getFirst f
                            (match es in Eventually ls0
                                   return Cons x ls' = ls0 -> Eventually ls' with
                               | Event_e x0 s' es' =>
                                 fun heq: Cons x ls' = Cons x0 s' =>
                                   eq_rect_r _ es' (injectionCons2 heq)
                               | Event_n x0 s' pf' =>
                                 fun heq =>
                                   match pp (eq_rect_r _ pf' (injectionCons1 heq)) with end
                             end heq)
                            (match als in AlwaysEventually ls0
                                   return Cons x ls' = ls0 -> AlwaysEventually ls' with
                               | AE_n x0 s' _ als' =>
                                 fun heq =>
                                   eq_rect_r _ als' (injectionCons2 heq)
                             end heq)
          end
    end eq_refl.

  Fixpoint getN f ls (als: AlwaysEventually ls) n :=
    match als with
      | AE_n x s' es als' =>
        match n with
          | 0 => sn (getFirst f es (AE_n es als'))
          | S m => getN f (alsThing (getFirst f es (AE_n es als'))) m
        end
    end.
End AlwaysEventually.
