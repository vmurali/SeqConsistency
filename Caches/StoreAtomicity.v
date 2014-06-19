Require Import DataTypes.

Set Implicit Arguments.

Record Resp := { addrR: Addr;
                 procR: Cache;
                 idx: Index;
                 datum: Data
               }.

Section StoreAtomicity.
  Variable reqFn: Addr -> Cache -> Index -> Req.

  Variable respFn: Time -> option Resp.

  Definition noStore a t :=
    match respFn t with
      | Some (Build_Resp a' c' i' d') =>
          a' = a -> desc (reqFn a c' i') = St -> False
      | _ => True
    end.

  Record StoreAtomicity :=
    {
      uniqRespLabels:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp a1 c1 i1 _), Some (Build_Resp a2 c2 i2 _) =>
                          a1 = a2 -> c1 = c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end;

      localOrdering:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp a1 c1 i1 _), Some (Build_Resp a2 c2 i2 _) =>
                          a1 = a2 -> c1 = c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end;

      allPrevious:
        forall t2, match respFn t2 with
                     | Some (Build_Resp a2 c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                        match respFn t1 with
                                                          | Some (Build_Resp a1 c1 i _) =>
                                                            a1 = a2 /\ c1 = c2 /\ i = i1
                                                          | None => False
                                                        end
                     | _ => True
                   end;

      storeAtomicity:
        forall t,
          match respFn t with
            | Some (Build_Resp a c i d) =>
              let (descQ, dtQ) := reqFn a c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore a t') \/
                  (exists tm,
                     tm < t /\
                     match respFn tm with
                       | Some (Build_Resp am cm im dm) =>
                         let (descQm, dtQm) := reqFn am cm im in
                         a = am /\ d = dtQm /\ descQm = St /\
                         forall t', tm < t' < t -> noStore a t'
                       | _ => False
                     end)
                | St => d = initData zero 
              end
            | _ => True
          end
  }.
End StoreAtomicity.
