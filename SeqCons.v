Require Import DataTypes.

Set Implicit Arguments.

Section SeqCons.
  Variable respFn: Time -> option Resp.

  Definition noStore a t :=
    match respFn t with
      | Some (Build_Resp c' i' d') =>
          addr (reqFn c' i') = a -> desc (reqFn c' i') = St -> False
      | _ => True
    end.

  Record SeqCons :=
    {
      uniqRespLabels:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          c1 = c2 -> i1 = i2 -> t1 = t2
                        | _, _ => True
                      end;

      localOrdering:
        forall t1 t2, match respFn t1, respFn t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          c1 = c2 -> i1 > i2 -> t1 > t2
                        | _, _ => True
                      end;

      allPrevious:
        forall t2, match respFn t2 with
                     | Some (Build_Resp c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                        match respFn t1 with
                                                          | Some (Build_Resp c1 i _) =>
                                                            c1 = c2 /\ i = i1
                                                          | None => False
                                                        end
                     | _ => True
                   end;

      seqCons:
        forall t,
          match respFn t with
            | Some (Build_Resp c i d) =>
              let (descQ, a, dtQ) := reqFn c i in
              match descQ with
                | Ld =>
                  (d = initData a /\ forall t', t' < t -> noStore a t') \/
                  (exists tm,
                     tm < t /\
                     match respFn tm with
                       | Some (Build_Resp cm im dm) =>
                         let (descQm, a, dtQm) := reqFn cm im in
                         d = dtQm /\ descQm = St /\
                         forall t', tm < t' < t -> noStore a t'
                       | _ => False
                     end)
                | St => d = initData zero 
              end
            | _ => True
          end
  }.
End SeqCons.
