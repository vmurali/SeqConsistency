Set Implicit Arguments.

Require Import AtomicReg AtomicRegIfc StoreAtomicity DataTypes NamedTrans.

Section ForAddr.
  Variable reqFn: Addr -> Proc -> Index -> Req.
  Variable respFn: Time -> option Resp.

  Variable sa: StoreAtomicity reqFn respFn.

  Record BehAtomicReg :=
    { atomicBeh: AtomicTransList reqFn (Build_State (initData) (fun a t => 0));
      respMatch: forall n, respFn n = getResp n atomicBeh
    }.

  Definition getNBeh n := getTransList (@getTransNext reqFn respFn) n.

  Definition saBehAtomicReg: BehAtomicReg.
  Proof.
    pose (buildAl reqFn respFn 0) as one.
    assert (two: forall n, respFn n = getResp n one).
    intros.
    pose proof (getRespEq sa n) as e1.
    pose proof (respEq sa n) as e2.
    rewrite <- e1 in e2.
    fold one in e2.
    assumption.
    apply (Build_BehAtomicReg one two).
  Defined.
End ForAddr.
