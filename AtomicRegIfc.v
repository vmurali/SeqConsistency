Set Implicit Arguments.

Require Import DataTypes StoreAtomicity.

Section ForAddr.
  Variable reqFn: Addr -> Proc -> Index -> Req.

  Record State := { mem: Addr -> Data;
                    next: Addr -> Proc -> Index
                  }.
  
  Inductive AtomicTrans s: State -> Set :=
  | AReq: forall a c, AtomicTrans s (Build_State
                                    (match desc (reqFn a c (next s a c)) with
                                       | Ld => mem s
                                       | St => fun a' =>
                                         if decAddr a a'
                                         then dataQ (reqFn a' c (next s a c))
                                         else mem s a'
                                     end)
                                    (fun a' t => 
                                       if decAddr a a'
                                       then
                                         match decProc t c with
                                                   | left _ => S (next s a' t)
                                                   | _ => next s a' t
                                         end
                                       else next s a' t
                                    ))
  | Idle: AtomicTrans s s.
  
  CoInductive AtomicTransList: State -> Set :=
    | TCons: forall s s', AtomicTrans s s' -> AtomicTransList s' -> AtomicTransList s.

End ForAddr.
