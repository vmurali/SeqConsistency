Set Implicit Arguments.

Require Import DataTypes StoreAtomicity Transitions.

Definition Cache := Proc.
Definition decTree := decProc.

Section ForAddr.
  Variable reqFn: Addr -> Cache -> Index -> Req.

  Record State := { mem: Addr -> Data;
                    next: Addr -> Cache -> Index
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
                                         match decTree t c with
                                                   | left _ => S (next s a' t)
                                                   | _ => next s a' t
                                         end
                                       else next s a' t
                                    ))
  | Idle: AtomicTrans s s.

End ForAddr.
