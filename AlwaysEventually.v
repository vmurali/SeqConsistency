Set Implicit Arguments.

Section AlwaysEventually.
  Variable A: Type.

  CoInductive Stream: Type :=
  | Cons: forall x: A, Stream -> Stream.

  Definition hdStream s :=
    match s with
      | Cons x _ => x
    end.

  Definition tlStream s :=
    match s with
      | Cons _ xs => xs
    end.

  Variable P: A -> Prop.
  Variable P_dec: forall x, {P x} + {~ P x}.
  Inductive Eventually: Stream -> Type :=
  | Event_e: forall x s, Eventually s -> Eventually (Cons x s)
  | Event_n: forall x s, P x -> Eventually (Cons x s).

  CoInductive AlwaysEventually: Stream -> Type :=
  | AE_n: forall x s, Eventually (Cons x s) -> AlwaysEventually s ->
                      AlwaysEventually (Cons x s).

  Record NextStream :=
    { ft: A;
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

  Fixpoint getFirst ls (es: Eventually ls) (als: AlwaysEventually ls) {struct es}: NextStream :=
    match ls as ls0 return ls0 = ls -> NextStream with
      | Cons x ls' =>
        fun heq: Cons x ls' = ls =>
          match P_dec x with
            | left pp => Build_NextStream
                           pp
                           (match als in AlwaysEventually ls0
                                  return
                                  Cons x ls' = ls0 -> AlwaysEventually ls' with
                              | AE_n x0 s' _ als' =>
                                fun heq => eq_rect_r _ als' (injectionCons2 heq)
                            end heq)
            | right pp => getFirst
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

  Fixpoint getN ls (als: AlwaysEventually ls) n :=
    match als with
      | AE_n x s' es als' =>
        match n with
          | 0 => ft (getFirst es (AE_n es als'))
          | S m => getN (alsThing (getFirst es (AE_n es als'))) m
        end
    end.
End AlwaysEventually.
