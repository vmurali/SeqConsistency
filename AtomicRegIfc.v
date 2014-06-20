Set Implicit Arguments.

Require Import DataTypes StoreAtomicity Transitions.

Definition Cache := Proc.
Definition decTree := decProc.

Section ForAddr.
  Record State := { mem: Addr -> Data;
                    next: Addr -> Cache -> Index
                  }.
  
  Inductive AtomicTrans s: State -> Set :=
  | AReq: forall a c d w, AtomicTrans s (Build_State
                                           (match w with
                                              | Ld => mem s
                                              | St => fun a' =>
                                                        if decAddr a a'
                                                        then d
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
