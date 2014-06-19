Require Import DataTypes Omega Coq.Logic.Classical MsiState.

Module Type L1Axioms (dt: DataTypes).
  Import dt.
  Axiom deqOrNot: forall t, {x| deqR (fst (fst x)) (snd (fst x)) (snd x) t} +
                            {forall a c i, ~ deqR a c i t}.
  Axiom deqLeaf: forall {c a i t}, deqR a c i t -> leaf c.
  Axiom deqDef: forall {c a i t}, deqR a c i t -> defined c.
  Axiom uniqDeqProc: forall {c a i1 t i2},
                       deqR a c i1 t -> deqR a c i2 t ->
                       i1 = i2.
  Axiom uniqDeqProc2: forall {c a i t1 t2},
                        deqR a c i t1 -> deqR a c i t2 -> t1 = t2.
  Axiom uniqDeqProc3: forall {c1 a1 i1 t c2 a2 i2},
                       deqR a1 c1 i1 t -> deqR a2 c2 i2 t ->
                       a1 = a2 /\ c1 = c2 /\ i1 = i2.
  Axiom deqOrder: forall {c a i1 t1 i2 t2},
                    deqR a c i1 t1 -> deqR a c i2 t2 ->
                    i1 < i2 -> ~ t1 > t2.
  Axiom processDeq: forall {c a i t}, deqR a c i t -> let q := reqFn a c i in
                                          match desc q with
                                            | Ld => sle Sh (state c a t)
                                            | St => state c a t = Mo
                                          end.
  Parameter deqImpDeqBefore: forall {c a i1 i2 t},
                               deqR a c i1 t -> i2 < i1 -> exists t', t' < t /\ deqR a c i2 t'.
End L1Axioms.

Module Type L1Theorems (dt: DataTypes) (l1A: L1Axioms dt).
  Import dt l1A.
  Parameter latestValue:
  forall {c a t},
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    (data c a t = initData a /\
     forall {ti}, 0 <= ti < t -> forall {ci ii},
                                   defined ci ->
                                   ~ (deqR a ci ii ti /\
                                      desc (reqFn a ci ii) = St)) \/
    (exists cb ib tb, defined cb /\ tb < t /\ deqR a cb ib tb /\ desc (reqFn a cb ib) = St /\
                      data c a t = dataQ (reqFn a cb ib) /\
                      forall {ti}, tb < ti < t ->
                                   forall {ci ii},
                                     defined ci ->
                                     ~ (deqR a ci ii ti /\
                                        desc (reqFn a ci ii) = St)
    ).

  Parameter uniqM:
  forall {c a t}, defined c -> leaf c ->
    state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.

  Parameter deqOrNot: forall t, {x| deqR (fst (fst x)) (snd (fst x)) (snd x) t} + {forall a c i, ~ deqR a c i t}.

End L1Theorems.
