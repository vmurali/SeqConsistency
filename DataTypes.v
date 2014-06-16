Set Implicit Arguments.

Require Import Arith.

Definition Time := nat.
Definition Index := nat.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall (a1 a2:Addr), {a1 = a2} + {a1 <> a2}.

Inductive Desc := Ld | St.

Parameter Data: Set.
Axiom decData: forall (d1 d2: Data), {d1 = d2} + {d1 <> d2}.

Parameter Proc: Set.
Axiom decProc: forall (p1 p2: Proc), {p1 = p2} + {p1 <> p2}.

Definition Tag := nat.
Definition decTag := eq_nat_dec.