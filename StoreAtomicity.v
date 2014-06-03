Require Import DataTypes.

Set Implicit Arguments.
Record Req := { desc: Desc;
                dataQ: Data
              }.

Record Resp := { procR: Proc;
                 idx: Index;
                 datum: Data
               }.

Section StoreAtomicity.
  Variable reqFn: Addr -> Proc -> Index -> Req.

  Variable respFn: Addr -> Time -> option Resp.

  Variable a: Addr.

  Definition noStore t :=
    match respFn a t with
      | Some (Build_Resp c' i' d') =>
          desc (reqFn a c' i') = St -> False
      | _ => True
    end.

  Record StoreAtomicity :=
    {
      uniqRespLabels:
        forall t1 t2, match respFn a t1, respFn a t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          c1 = c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end;

      localOrdering:
        forall t1 t2, match respFn a t1, respFn a t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          c1 = c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end;

      allPrevious:
        forall t2, match respFn a t2 with
                     | Some (Build_Resp c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                        match respFn a t1 with
                                                          | Some (Build_Resp c1 i _) =>
                                                            c1 = c2 /\ i = i1
                                                          | None => False
                                                        end
                     | _ => True
                   end;

      storeAtomicity:
        forall t,
          match respFn a t with
            | Some (Build_Resp c i d) =>
              let (descQ, dtQ) := reqFn a c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore t') \/
                  (exists tm,
                     tm < t /\
                     match respFn a tm with
                       | Some (Build_Resp cm im dm) =>
                         let (descQm, dtQm) := reqFn a cm im in
                         d = dtQm /\ descQm = St /\
                         forall t', tm < t' < t -> noStore t'
                       | _ => False
                     end)
                | St => d = initData zero 
              end
            | _ => True
          end
  }.
End StoreAtomicity.
