Set Implicit Arguments.

Require Import AtomicReg AtomicRegIfc StoreAtomicity DataTypes.

Section ForAddr.
  Variable reqFn: Addr -> Proc -> Index -> Req.
  Variable respFn: Addr -> Time -> option Resp.
  Variable a: Addr.

  Variable sa: StoreAtomicity reqFn respFn a.

  Theorem storeAtomicityImpAtomicRegBehavior n :
    exists (al: AtomicTransList reqFn a (Build_State (initData a) (fun t => 0))),
      respFn a n = getResp n al.
  Proof.
    exists (buildAl reqFn respFn a 0).
    pose proof (getRespEq reqFn respFn a n) as e1.
    pose proof (respEq sa n) as e2.
    rewrite <- e1 in e2.
    assumption.
  Qed.
End ForAddr.

Print Assumptions storeAtomicityImpAtomicRegBehavior.

About storeAtomicityImpAtomicRegBehavior.