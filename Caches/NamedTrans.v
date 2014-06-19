Set Implicit Arguments.

Section NamedTrans.
  Variable State: Set.
  Variable Trans: State -> State -> Set.
  Variable init: State.

  Inductive TransList: nat -> State -> Set :=
    | Init: TransList 0 init
    | Next:
        forall n s,
          TransList n s ->
          forall s' (t: Trans s s'),
            TransList (S n) s'.

  Record NextTrans s : Set := { st: State;
                                trans: Trans s st}.

  Variable (getTransNext: forall n s, TransList n s -> NextTrans s).

  Record NextList n : Set := { lSt: State;
                               lTrans: TransList n lSt}.

  Fixpoint getTransList n :=
    match n as n0 return NextList n0 with
      | 0 => Build_NextList Init
      | S k =>
        let ls := lTrans (getTransList k) in
        let t := getTransNext ls in
        Build_NextList (Next ls (trans t))
    end.

  Definition getTransSt n := lSt (getTransList n).

  Definition getTrans n := trans (getTransNext (lTrans (getTransList n))).
End NamedTrans.
