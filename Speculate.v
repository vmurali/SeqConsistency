Set Implicit Arguments.

Require Import DataTypes.
Require Import List.
Require Import Arith.

Parameter Op: Set.

Inductive Inst :=
| Load: Addr -> Inst
| Store: Addr -> Data -> Inst
| NonMem: Op -> Inst.

Inductive HElem :=
| Ld: Addr -> Data -> HElem
| St: Addr -> Data -> HElem
| Nm: Op -> HElem.

Definition Hist := list HElem.

Inductive SElem :=
| Sld: Addr -> SElem
| Sst: Addr -> Data -> SElem
| Snm: Op -> SElem
| Sfl: Addr -> Data -> SElem.

Definition SHist := list (nat * SElem).

Parameter prog: Proc -> Hist -> Inst.

Fixpoint nGet n (s: SHist) :=
  match s with
    | (m, x) :: xs => if eq_nat_dec n m then Some x else nGet n xs
    | nil => None
  end.

Fixpoint nRm n (s: SHist) :=
  match s with
    | (m, x) :: xs => if eq_nat_dec n m then xs else (m, x) :: nRm n xs
    | nil => nil
  end.

Inductive Spec (p: Proc) : Hist -> SHist -> Set :=
| SpecInit: Spec p nil nil
(* Speculative load issue *)
| SpecLd: forall n a h s, Spec p h s -> Spec p h ((n, Sld a) :: s)
(* Speculative store issue *)
| SpecSt: forall n a v h s, Spec p h s -> Spec p h ((n, Sst a v) :: s)
(* Speculative non mem issue *)
| SpecNm: forall n o h s, Spec p h s -> Spec p h ((n, Snm o) :: s)
(* Speculative load completion *)
| SpecFl: forall n a v h s, Spec p h s -> nGet n s = Some (Sld a) -> Spec p h ((n, Sfl a v) :: s)
(* Commit a load (request and response) and remove corresponding speculative issue *)
| CLd: forall n a v v' h s, Spec p h s -> nGet n s = Some (Sfl a v') -> prog p h = Load a ->
                            Spec p (Ld a v :: h) (nRm n s)
(* Commit a store and remove corresponding speculative issue *)
| CSt: forall n a v h s, Spec p h s -> nGet n s = Some (Sst a v) -> prog p h = Store a v ->
                         Spec p (St a v :: h) (nRm n s)
(* Commit a non mem and remove corresponding speculative issue *)
| CNm: forall n o h s, Spec p h s -> nGet n s = Some (Snm o) -> prog p h = NonMem o ->
                       Spec p (Nm o :: h) (nRm n s)
(* Kill a speculative issue *)
| Kill: forall n h s, Spec p h s -> Spec p h (nRm n s).

Definition Mem := Addr -> Data.
Definition updM a (d: Data) mem := fun a' => if decAddr a a' then d else mem a'.

Definition updP p h s (x: Spec p h s) ps := fun p' => if decProc p p' then x else ps p'.

Inductive SpecSc: forall h s, (forall p, Spec p h s) -> Mem -> Set :=
| SpcInit: forall m, SpecSc (fun p => SpecInit p) m
| SpcLd: forall ps (p: Proc) m n a h s, SpecSc ps m -> SpecSc (updP (SpecLd n a (ps p)) ps) m.

Inductive Proc : Hist -> Set :=
| ProcInit: Proc nil
| ProcLd: forall a v h, Proc h -> prog h = Load a -> Proc (Ld a v :: h)
| ProcSt: forall a v h, Proc h -> prog h = Store a v -> Proc (St a v :: h)
| ProcNm: forall op h, Proc h -> prog h = NonMem op -> Proc (Nm op :: h).

Inductive SeqCons : forall h, Proc h -> Mem -> Set :=
| SqInit: forall m, SeqCons ProcInit m
| SqLd: forall h (p: Proc h) m a (pf: prog h = Load a), SeqCons p m -> SeqCons (ProcLd (m a) p pf) m
| SqSt: forall h (p: Proc h) m a v (pf: prog h = Store a v),
          SeqCons p m -> SeqCons (ProcSt p pf) (upd a v m)
| SqNm: forall h (p: Proc h) m o (pf: prog h = NonMem o), SeqCons p m -> SeqCons (ProcNm p pf) m.

Inductive Sc : forall h s, Spec h s -> Mem -> Set :=
| ScInit: forall m, Sc SpecInit m
| ScLd: forall h s (p: Spec h s) m a n, Sc p m -> Sc (SpecLd n a p) m
| ScSt: forall h