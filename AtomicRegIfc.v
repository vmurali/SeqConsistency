Set Implicit Arguments.

Require Import DataTypes StoreAtomicity.

Section ForAddr.
  Variable reqFn: Addr -> Proc -> Index -> Req.
  Variable a: Addr.

  Record State := { mem: Data;
                    next: Proc -> Index
                  }.
  
  Inductive AtomicTrans s: State -> Set :=
  | AReq: forall c, AtomicTrans s (Build_State
                                    (match desc (reqFn a c (next s c)) with
                                       | Ld => mem s
                                       | St => dataQ (reqFn a c (next s c))
                                     end)
                                    (fun t => match decProc t c with
                                                | left _ => S (next s t)
                                                | _ => next s t
                                              end))
  | Idle: AtomicTrans s s.
  
  CoInductive AtomicTransList: State -> Set :=
    | Cons: forall s s', AtomicTrans s s' -> AtomicTransList s' -> AtomicTransList s.

End ForAddr.
