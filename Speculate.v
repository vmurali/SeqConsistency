Set Implicit Arguments.

Require Import DataTypes.
Require Import List.
Require Import Arith.
Require Import Tree.

Inductive Req :=
| LdReq: nat -> Addr -> Req
| StReq: Addr -> Data -> Req.

Inductive Resp :=
| LdResp: nat -> Data -> Resp.

Inductive Inst :=
| Load: Addr -> Inst
| Store: Addr -> Data -> Inst.

Inductive HElem :=
| Ld: Addr -> Data -> HElem
| St: Addr -> Data -> HElem.

Definition Hist := list HElem.

Definition Mem := Addr -> Data.

Inductive SElem :=
| Sld: Addr -> SElem
| Sst: Addr -> Data -> SElem
| Sfl: Addr -> Data -> SElem.

Definition SHist := list (nat * SElem).

Axiom decProc: forall (p1 p2: Proc), {p1 = p2} + {p1 <> p2}.

Section GivenProg.
  Variable prog: Proc -> Hist -> Inst.
  Variable m0: Mem.

  Definition mod A st p (new: A) p' :=
    if decProc p p' then new else st p'.

  Record PerProcState :=
    { hist: Hist;
      qs: list Req;
      rs: list Resp
    }.
             
  Inductive Normal: (Proc -> PerProcState) -> Mem -> Prop :=
  | Init: Normal (fun p => Build_PerProcState nil nil nil) m0
  | NormalLd: forall st m p a,
                let stp := st p in
                Normal st m ->
                prog p (hist stp) = Load a ->
                Normal (mod st p (Build_PerProcState (Ld a (m a) :: hist stp) (LdReq 0 a :: qs stp) (LdResp 0 (m a) :: rs stp))) m
  | NormalSt: forall st m p a v,
                let stp := st p in
                Normal st m ->
                prog p (hist stp) = Store a v ->
                Normal (mod st p (Build_PerProcState (St a v :: hist stp) (StReq a v :: qs stp) (rs stp))) m.

  Record PerProcSpecState :=
    { hist': Hist;
      spec: SHist;
      tag: nat;
      qs': list Req;
      rs': list Resp
    }.

  Fixpoint updS A s n (op: A) :=
    match s with
      | nil => nil
      | (m, x) :: xs => if eq_nat_dec m n then (m, op) :: xs else (m, x) :: updS xs n op
    end.

  Fixpoint rmS A (s: list (nat * A)) n :=
    match s with
      | nil => nil
      | (m, x) :: xs => if eq_nat_dec m n then xs else (m, x) :: rmS xs n
    end.

  Fixpoint oldest A (s: list A) :=
    match s with
      | nil => None
      | x :: nil => Some x
      | x :: xs => oldest xs
    end.

  Inductive Spec: (Proc -> PerProcSpecState) -> Mem -> Prop :=
  | SpecInit: Spec (fun p => Build_PerProcSpecState nil nil 0 nil nil) m0
  | SpecLdReq: forall st m p a,
                 let stp := st p in
                 Spec st m ->
                 Spec (mod st p (Build_PerProcSpecState (hist' stp) ((tag stp, Sld a) :: spec stp) (S (tag stp)) (LdReq (tag stp) a :: qs' stp) (rs' stp))) m
  | SpecLdResp: forall st m p a n' v,
                 let stp := st p in
                 Spec st m ->
                 Spec (mod st p (Build_PerProcSpecState (hist' stp) (updS (spec stp) n' (Sfl a v)) (tag stp) (qs' stp) (LdResp n' v :: rs' stp))) m
  | SpecLdCommit: forall st m p a n',
                    let stp := st p in
                    Spec st m ->
                    oldest (spec stp) = Some (n', (Sfl a (m a))) ->
                    prog p (hist' stp) = Load a ->
                    Spec (mod st p (Build_PerProcSpecState (Ld a (m a) :: hist' stp) (rmS (spec stp) n') (S (tag stp)) (LdReq (tag stp) a :: qs' stp) (LdResp (tag stp) (m a) :: rs' stp))) m
  | SpecLdCommitBad: forall st m p a n' v,
                       let stp := st p in
                       Spec st m ->
                       oldest (spec stp) = Some (n', (Sfl a v)) ->
                       v <> m a ->
                       prog p (hist' stp) = Load a ->
                       Spec (mod st p (Build_PerProcSpecState (Ld a (m a) :: hist' stp) nil (S (tag stp)) (LdReq (tag stp) a :: qs' stp) (LdResp (tag stp) (m a) :: rs' stp))) m
  | SpecStCommit: forall st m p a n' v,
                    let stp := st p in
                    Spec st m ->
                    oldest (spec stp) = Some (n', (Sst a v)) ->
                    prog p (hist' stp) = Store a v ->
                    Spec (mod st p (Build_PerProcSpecState (St a v :: hist' stp) (rmS (spec stp) n') (tag stp) (StReq a v :: qs' stp) (rs' stp))) m
  | SpecAbort: forall st m p n',
                   let stp := st p in
                   Spec st m ->
                   Spec (mod st p (Build_PerProcSpecState (hist' stp) (rmS (spec stp) n')
                                                          (tag stp) (qs' stp) (rs' stp))) m.

Theorem specIsSc:
  forall st' m, Spec st' m -> exists st, (forall p, hist' (st' p) = hist (st p)) /\ Normal st m.
Proof.
  intros.
  induction H.
  Ltac common x IHSpec := (try exists (fun p => Build_PerProcState nil nil nil); intuition; constructor)
    || (
    destruct IHSpec;
    exists x;
    constructor;
    [ intros;
      unfold mod;
      match goal with
        | _: _ |- context [decProc ?p ?p0] =>
          destruct (decProc p p0) as [e | n]; simpl; intuition;
          rewrite <- e in *;
          match goal with
            | H1: forall p: Proc, _ = _ |- _ => specialize (H1 p)
          end;
          intuition
      end| 
      intuition]).

  common x IHSpec.
  common x IHSpec.
  common x IHSpec.

  destruct IHSpec.
  destruct H2.
  pose proof (H2 p) as K.
  unfold stp in H1.
  rewrite K in H1.
  pose proof (NormalLd H3 H1).
  exists (mod x p
              {|
                hist := Ld a (m a) :: hist (x p);
                qs := LdReq 0 a :: qs (x p);
                rs := LdResp 0 (m a) :: rs (x p) |}).
  constructor.
  intros.
  unfold mod.
  destruct (decProc p p0); simpl; intuition.
  unfold stp.
  rewrite K.
  reflexivity.
  intuition.

  destruct IHSpec.
  destruct H3.
  pose proof (H3 p) as K.
  unfold stp in H2.
  rewrite K in H2.
  pose proof (NormalLd H4 H2).
  exists (mod x p
              {|
                hist := Ld a (m a) :: hist (x p);
                qs := LdReq 0 a :: qs (x p);
                rs := LdResp 0 (m a) :: rs (x p) |}).
  constructor.
  intros.
  unfold mod.
  destruct (decProc p p0); simpl; intuition.
  unfold stp.
  rewrite K.
  reflexivity.
  intuition.

  destruct IHSpec.
  destruct H2.
  pose proof (H2 p) as K.
  unfold stp in H1.
  rewrite K in H1.
  pose proof (NormalSt H3 H1).
  exists (mod x p
              {|
                hist := St a v :: hist (x p);
                qs := StReq a v :: qs (x p);
                rs := rs (x p) |}).
  constructor.
  intros.
  unfold mod.
  destruct (decProc p p0); simpl; intuition.
  unfold stp.
  rewrite K.
  reflexivity.
  intuition.

  common x IHSpec.
Qed.

End GivenProg.
