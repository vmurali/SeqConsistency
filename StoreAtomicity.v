Require Import DataTypes.

Set Implicit Arguments.

Section StoreAtomicity.
  Record ReqA := { descA: Desc;
                   dataAQ: Data
                 }.

  Record RespA := { procAR: Proc;
                    idxA: Index;
                    datumA: Data
                  }.

  Parameter reqFnA: Addr -> Proc -> Index -> ReqA.

  Variable respFnA: Addr -> Time -> option RespA.

  Variable a: Addr.

  Definition noStore t :=
    match respFnA a t with
      | Some (Build_RespA c' i' d') =>
          descA (reqFnA a c' i') = St -> False
      | _ => True
    end.

  Record StoreAtomicity :=
    {
      uniqRespLabels:
        forall t1 t2, match respFnA a t1, respFnA a t2 with
                        | Some (Build_RespA c1 i1 _), Some (Build_RespA c2 i2 _) =>
                          c1 = c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end;

      localOrdering:
        forall t1 t2, match respFnA a t1, respFnA a t2 with
                        | Some (Build_RespA c1 i1 _), Some (Build_RespA c2 i2 _) =>
                          c1 = c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end;

      allPrevious:
        forall t2, match respFnA a t2 with
                     | Some (Build_RespA c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                        match respFnA a t1 with
                                                          | Some (Build_RespA c1 i _) =>
                                                            c1 = c2 /\ i = i1
                                                          | None => False
                                                        end
                     | _ => True
                   end;

      storeAtomicity:
        forall t,
          match respFnA a t with
            | Some (Build_RespA c i d) =>
              let (descQ, dtQ) := reqFnA a c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore t') \/
                  (exists tm,
                     tm < t /\
                     match respFnA a tm with
                       | Some (Build_RespA cm im dm) =>
                         let (descQm, dtQm) := reqFnA a cm im in
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
