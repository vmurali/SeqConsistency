Require Import StoreAtomicity DataTypes.

Inductive AtomicMemory : (Addr -> Data) -> (Addr -> Data) -> Set :=
| AReq m a (w: Desc) d: AtomicMemory m
                                     (if w
                                      then m
                                      else fun a' => if decAddr a a'
                                                     then d
                                                     else m a')
| Idle m: AtomicMemory m m.

Definition getAtomicMemoryInfo m m' (am: AtomicMemory m m') :=
  match am with
    | AReq _ a w d => Some (a, w, d, if w
                                     then m a
                                     else initData zero)
    | Idle _ => None
  end.

Section ReqResp.
  Variable reqFn: Addr -> Proc -> Index -> Req.
  Variable respFn: Time -> option Resp.

  Variable sa: StoreAtomicity reqFn respFn.

  
End ReqResp.