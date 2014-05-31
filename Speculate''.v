Set Implicit Arguments.

Require Import DataTypes.
Require Import List.
Require Import Arith.

Parameter Op: Set.

Inductive Inst :=
| Load: Addr -> Inst
| Store: Addr -> Data -> Inst.

Inductive HElem :=
| Ld: Addr -> Data -> HElem
| St: Addr -> Data -> HElem.

Definition Hist := list HElem.

Inductive SElem :=
| Sld: Addr -> SElem
| Sst: Addr -> Data -> SElem
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

Definition appP A p (new: A) lsp p' :=
  if decProc p p' then new :: lsp p' else lsp p'.

Definition rmSP p n ls p' :=
  if decProc p p' then nRm n (ls p') else ls p'.

Definition incP p ns p' :=
  if decProc p p' then S (ns p') else ns p'.

Definition Mem := Addr -> Data.
Definition updM a (d: Data) mem := fun a' => if decAddr a a' then d else mem a'.
Parameter m0: Mem.

Inductive Spec: (Proc -> Hist) -> (Proc -> SHist) -> (Proc -> nat) -> Mem -> Set :=
| SpecInit: Spec (fun p => nil) (fun p => nil) (fun p => 0) m0
(* Speculative load issue *)
| SpecLd: forall p h s n a m, Spec h s n m -> Spec h (appP p (n p, Sld a) s) (incP p n) m
(* Speculative store issue *)
| SpecSt: forall p h s n a v m, Spec h s n m -> Spec h (appP p (n p, Sst a v) s) (incP p n) m
(* Speculative load completion *)
| SpecFl: forall p h s n a m, Spec h s n m -> nGet (n p) (s p) = Some (Sld a) ->
                              Spec h (appP p (n p, Sfl a (m a)) s) n m
(* Commit a load (request and response) and remove corresponding speculative issue *)
| CLd: forall p h s n a v m, Spec h s n m -> nGet (n p) (s p) = Some (Sfl a v) -> prog p (h p) = Load a ->
                             Spec (appP p (Ld a (m a)) h) (rmSP p (n p) s) n m
(* Commit a store and remove corresponding speculative issue *)
| CSt: forall p h s n a v m, Spec h s n m -> nGet (n p) (s p) = Some (Sst a v) -> prog p (h p) = Store a v ->
                             Spec (appP p (St a v) h) (rmSP p (n p) s) n (updM a v m)
(* Kill a speculative issue *)
| Kill: forall p h s n n' m, Spec h s n m -> Spec h (rmSP p n' s) n m.

Inductive Simple: (Proc -> Hist) -> Mem -> Prop :=
| Init: Simple (fun p => nil) m0
| SimpleLd: forall p h a m, Simple h m -> prog p (h p) = Load a -> Simple (appP p (Ld a (m a)) h) m
| SimpleSt: forall p h a v m, Simple h m -> prog p (h p) = Store a v -> Simple (appP p (St a v) h) (updM a v m).

Theorem specIsSc:
  forall h s n m, Spec h s n m -> Simple h m.
Proof.
  intros;
    match goal with
      | H: Spec _ _ _ _ |- _ => induction H; try constructor; assumption
    end.
Qed.
