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

Inductive Spec: (Proc -> Hist) -> (Proc -> SHist) -> (Proc -> nat) -> Set :=
| SpecInit: Spec (fun p => nil) (fun p => nil) (fun p => 0)
(* Speculative load issue *)
| SpecLd: forall p h s n a, Spec h s n -> Spec h (appP p (n p, Sld a) s) (incP p n)
(* Speculative store issue *)
| SpecSt: forall p h s n a v, Spec h s n -> Spec h (appP p (n p, Sst a v) s) (incP p n)
(* Speculative load completion *)
| SpecFl: forall p h s n a v, Spec h s n -> nGet (n p) (s p) = Some (Sld a) -> Spec h (appP p (n p, Sfl a v) s) n
(* Commit a load (request and response) and remove corresponding speculative issue *)
| CLd: forall p h s n a v v', Spec h s n -> nGet (n p) (s p) = Some (Sfl a v') -> prog p (h p) = Load a ->
                              Spec (appP p (Ld a v) h) (rmSP p (n p) s) n
(* Commit a store and remove corresponding speculative issue *)
| CSt: forall p h s n a v, Spec h s n -> nGet (n p) (s p) = Some (Sst a v) -> prog p (h p) = Store a v ->
                           Spec (appP p (St a v) h) (rmSP p (n p) s) n
(* Kill a speculative issue *)
| Kill: forall p h s n n', Spec h s n -> Spec h (rmSP p n' s) n.

Definition Mem := Addr -> Data.
Definition updM a (d: Data) mem := fun a' => if decAddr a a' then d else mem a'.

Parameter m0: Mem.

Inductive Sc: forall h s n, Spec h s n -> Mem -> Prop :=
| ScInit: Sc SpecInit m0
| ScSpecLd: forall p h s n a (prev: Spec h s n) m, Sc prev m -> Sc (SpecLd p a prev) m
| ScSpecSt: forall p h s n a v (prev: Spec h s n) m, Sc prev m -> Sc (SpecSt p a v prev) m
| ScSpecFl: forall p h s n a (prev: Spec h s n) (mtch: nGet (n p) (s p) = Some (Sld a)) m,
              Sc prev m -> Sc (SpecFl p (m a) prev mtch) m
| ScCLd: forall p h s n a v' (prev: Spec h s n) (mtch: nGet (n p) (s p) = Some (Sfl a v'))
                (pg: prog p (h p) = Load a) m,
           Sc prev m -> Sc (CLd (m a) prev mtch pg) m
| ScCSt: forall p h s n a v (prev: Spec h s n) (mtch: nGet (n p) (s p) = Some (Sst a v))
                (pg: prog p (h p) = Store a v) m,
           Sc prev m -> Sc (CSt prev mtch pg) (updM a v m)
| ScKill: forall p h s n n' (prev: Spec h s n) m, Sc prev m -> Sc (Kill p n' prev) m.

Inductive Simple: (Proc -> Hist) -> Mem -> Prop :=
| Init: Simple (fun p => nil) m0
| SimpleLd: forall p h a m, Simple h m -> prog p (h p) = Load a -> Simple (appP p (Ld a (m a)) h) m
| SimpleSt: forall p h a v m, Simple h m -> prog p (h p) = Store a v -> Simple (appP p (St a v) h) (updM a v m).

Theorem specIsSc:
  forall h s n (p: Spec h s n) m, Sc p m -> Simple h m.
Proof.
  intros;
    match goal with
      | H: Sc _ _ |- _ => induction H ; try constructor; intuition
    end.
Qed.
