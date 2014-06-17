Set Implicit Arguments.

Section AlwaysEventually.
  Variable State: Set.
  Variable Trans: State -> State -> Set.

  CoInductive TransStream: State -> Set :=
  | TCons: forall s s' (t: Trans s s'), TransStream s' -> TransStream s.

  Variable P: forall s s', Trans s s' -> Prop.
  Variable P_dec: forall s s' (ts: Trans s s'), {P ts} + {~ P ts}.

  Inductive Eventually: forall s s', TransStream s -> TransStream s' -> Type :=
  | Later: forall s s1 (t: Trans s s1) ts s' (ts': TransStream s'),
             ~ P t -> Eventually ts ts' -> Eventually (TCons t ts) ts'
  | Now: forall s s' (t: Trans s s') ts, P t -> Eventually (TCons t ts) ts.

  CoInductive AlwaysEventually: forall s, TransStream s -> Type :=
  | Final: forall s (ts: TransStream s) s' (ts': TransStream s'), Eventually ts ts' ->
                                                                  AlwaysEventually ts' ->
                                                                  AlwaysEventually ts.

  Fixpoint getFirstTransState s (ts: TransStream s) s' (ts': TransStream s')
          (es: Eventually ts ts'): State * State :=
    match es with
      | Now s s' _ _ _ => (s, s')
      | Later _ _ _ _ _ _ _ es' => getFirstTransState es'
    end.

  Fixpoint getFirstTrans s (ts: TransStream s) s' (ts': TransStream s')
          (es: Eventually ts ts'):
    Trans (fst (getFirstTransState es)) (snd (getFirstTransState es)) :=
    match es with
      | Now _ _ t _ _ => t
      | Later _ _ _ _ _ _ _ es' => getFirstTrans es'
    end.

  Fixpoint getNState s (ts: TransStream s) (als: AlwaysEventually ts) (n: nat): State * State :=
    match als with
      | Final _ _ _ _ es als' =>
        match n with
          | 0 => getFirstTransState es
          | S m => getNState als' m
        end
    end.

  Fixpoint getNTrans s (ts: TransStream s) (als: AlwaysEventually ts) (n: nat):
    Trans (fst (getNState als n)) (snd (getNState als n)):=
    match als with
      | Final _ _ _ _ es als' =>
        match n with
          | 0 => getFirstTrans es
          | S m => getNTrans als' m
        end
    end.
End AlwaysEventually.
