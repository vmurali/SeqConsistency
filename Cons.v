Require Import DataTypes.
Require Import List.

Definition Tag := nat.

Inductive Req :=
| LdCommitReq: Addr -> Req
| LdReq: Tag -> Addr -> Req
| StReq: Addr -> Data -> Req.

Inductive Resp :=
| LdCommitResp: Data -> Resp
| LdResp: Tag -> Data -> Resp
| StResp: Resp.

Inductive Inst :=
| Nm: Inst
| Ld: Addr -> Inst
| St: Addr -> Data -> Inst.

Section PerProc.
  Parameter Pc: Set.
  Parameter State: Set.
  Parameter DeltaState: Set.

  Parameter nextSt: Pc -> option Data -> (Pc * Inst * DeltaState).
  Parameter updSt: State -> DeltaState -> State.

  Inductive Normal: State -> Pc -> list Req -> list Resp -> bool ->
                    State -> Pc -> list Req -> list Resp -> bool -> Set :=
  | ComNonMem: forall s nextPc p2m m2p nextPc' delS,
                 nextSt nextPc None = (nextPc', Nm, delS) ->
                 Normal s nextPc p2m m2p false (updSt s delS) nextPc' p2m m2p false
  | ComSt: forall s nextPc p2m m2p nextPc' delS a v,
             nextSt nextPc None = (nextPc', St a v, delS) ->
             Normal s nextPc p2m m2p false (updSt s delS) nextPc' (StReq a v :: p2m) m2p true
  | ComStRp: forall s nextPc p2m m2p,
               Normal s nextPc p2m (StResp :: m2p) true s nextPc p2m m2p false
  | ComLd: forall s nextPc p2m m2p nextPc' delS a,
             nextSt nextPc None = (nextPc', Ld a, delS) ->
             Normal s nextPc p2m m2p false s nextPc (LdCommitReq a :: p2m) m2p true
  | ComLdRp:
      forall s nextPc p2m m2p nextPc' delS a v,
        nextSt nextPc (Some v) = (nextPc', Ld a, delS) ->
        Normal s nextPc p2m (LdCommitResp v :: m2p) true (updSt s delS) nextPc' p2m m2p false
  | ExternalReq:
      forall s nextPc p2m m2p x w,
        Normal s nextPc (p2m ++ (x :: nil)) m2p w s nextPc p2m m2p w
  | ExternalResp:
      forall s nextPc p2m m2p x w,
        Normal s nextPc p2m (m2p ++ (x :: nil)) w s nextPc p2m m2p w.

  Parameter Rob: Set.

  Inductive Spec: State -> Pc -> Rob -> list Req -> list Resp ->
                  State -> Pc -> Rob -> list Req -> list Resp 
End PerProc.