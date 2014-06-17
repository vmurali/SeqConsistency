Require Import StoreAtomicity DataTypes.

Section ReqResp.
  Variable reqFn: Addr -> Proc -> Index -> Req.
  Variable respFn: Time -> option Resp.

  Inductive AtomicMemory : (Addr -> Proc) -> (Addr -> Proc) -> Set :=
  | AReq: forall m a (w: Desc) d, AtomicMemory m
                                               (if w
                                                then m
                                                else fun a' => if decAddr a a'
                                                               then d
                                                               else m a')
  | Idle: forall m, AtomicMemory m m.

  