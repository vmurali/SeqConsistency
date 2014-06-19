Set Implicit Arguments.

Require Import AtomicReg AtomicRegIfc StoreAtomicity DataTypes.

Section ForAddr.
  Variable reqFn: Addr -> Cache -> Index -> Req.
  Variable respFn: Time -> option Resp.

  Variable sa: StoreAtomicity reqFn respFn.

  Theorem storeAtomicityImpAtomicRegBehavior n :
    exists (al: AtomicTransList reqFn (Build_State (initData) (fun a t => 0))),
      respFn n = getResp n al.
  Proof.
    exists (buildAl reqFn respFn 0).
    About getRespEq.
    pose proof (getRespEq sa n) as e1.
    pose proof (respEq sa n) as e2.
    rewrite <- e1 in e2.
    assumption.
  Qed.
End ForAddr.

Print Assumptions storeAtomicityImpAtomicRegBehavior.

About storeAtomicityImpAtomicRegBehavior.