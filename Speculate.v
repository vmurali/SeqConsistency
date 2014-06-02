Set Implicit Arguments.

Require Import DataTypes.
Require Import List.

Inductive Req :=
| LdReq: Tag -> Addr -> Req
| StReq: Addr -> Data -> Req.

Inductive Resp :=
| LdResp: Tag -> Data -> Resp.

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

Definition SHist := list (Tag * SElem).

Section GivenProg.
  Variable prog: Proc -> Hist -> Inst.

  Definition mod A st p (new: A) p' :=
    if decProc p p' then new else st p'.

  Record PerProcState :=
    { hist: Hist;
      qs: list Req;
      rs: list Resp
    }.
             
  Inductive Normal: (Proc -> PerProcState) -> Mem -> Prop :=
  | Init: Normal (fun p => Build_PerProcState nil nil nil) initData
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
      tag: Tag;
      qs': list Req;
      rs': list Resp
    }.

  Fixpoint updS A s n (op: A) :=
    match s with
      | nil => nil
      | (m, x) :: xs => if decTag m n then (m, op) :: xs else (m, x) :: updS xs n op
    end.

  Fixpoint rmS A (s: list (Tag * A)) n :=
    match s with
      | nil => nil
      | (m, x) :: xs => if decTag m n then xs else (m, x) :: rmS xs n
    end.

  Fixpoint oldest A (s: list A) :=
    match s with
      | nil => None
      | x :: nil => Some x
      | x :: xs => oldest xs
    end.

  Inductive Spec: (Proc -> PerProcSpecState) -> Mem -> Prop :=
  | SpecInit: Spec (fun p => Build_PerProcSpecState nil nil 0 nil nil) initData
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

  Ltac comm IHSpec :=
    destruct IHSpec as [x [r1 r2]];
    match goal with
      | p: Proc , stp: PerProcSpecState |- _ =>
          let K := fresh in pose proof (r1 p) as K; unfold stp in *; rewrite K in *
    end;
    match goal with
      | H: prog _ _ = Load _ |- _ => pose proof (NormalLd r2 H)
      | H: prog _ _ = Store _ _ |- _ => pose proof (NormalSt r2 H)
      | _ => idtac
    end;
    match goal with
      | H: Normal ?x ?m, x: Proc -> PerProcState, H2: Normal ?y ?m |- _ =>
          exists y; unfold mod in *
      | _: Normal ?x ?m |- _ => exists x; unfold mod in *
    end;
    constructor; intros;
    match goal with
      | |- context [decProc ?p ?p0] =>
          let ep := fresh in
            let np := fresh in
              destruct (decProc p p0) as [ep|np]; simpl; try (rewrite ep in *)
      | _ => idtac
    end; intuition.

  induction H;
    (exists (fun p => Build_PerProcState nil nil nil); intuition; constructor) || comm IHSpec.
Qed.

End GivenProg.
