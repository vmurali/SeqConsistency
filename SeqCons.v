Require Import DataTypes.

Set Implicit Arguments.

Section StoreAtomicity.
  Variable a: Addr.
  Variable respFn: Time -> option Resp.

(*
  Definition noStore t :=
    match respFn t with
      | Some (Build_Resp c' i' d') =>
          desc (reqFn c' i') = St -> False
      | _ => True
    end.
*)

  Record StoreAtomicity :=
    {
      uniqRespLabels:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          p_node c1 = p_node c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end;

      localOrdering:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          p_node c1 = p_node c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end;

      allPrevious:
        forall t2, match respFn t2 with
                     | Some (Build_Resp c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                        match respFn t1 with
                                                          | Some (Build_Resp c1 i _) =>
                                                            p_node c1 = p_node c2 /\ i = i1
                                                          | None => False
                                                        end
                     | _ => True
                   end
    }.

(*
      storeAtomicity:
        forall t,
          match respFn t with
            | Some (Build_Resp c i d) =>
              let (descQ, dtQ) := reqFn a c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore t') \/
                  (exists tm,
                     tm < t /\
                     match respFn tm with
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
*)
End StoreAtomicity.
