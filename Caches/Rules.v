Require Import DataTypes Coq.Lists.Streams Coq.Logic.Classical_Prop Tree List MsiState Coq.Relations.Relation_Operators Transitions.

Record BaseMesg :=
  { fromB: State;
    toB: State;
    addrB: Addr;
    dataBM: Data;
    type: ChannelType
  }.

Record GlobalState :=
  { dt: Cache -> Addr -> Data;
    ch: ChannelType -> Cache -> Cache -> list BaseMesg;
    st: Cache -> Addr -> State;
    dirSt: Cache -> Cache -> Addr -> State;
    wt: Cache -> Addr -> bool;
    wtS: Cache -> Addr -> State;
    dirWt: Cache -> Cache -> Addr -> bool;
    dirWtS: Cache -> Cache -> Addr -> State
  }.

Definition dmy := Build_BaseMesg In In zero (initData zero) mch.

Inductive Transition (s: GlobalState) : GlobalState -> Set :=
| LoadReq: forall {c a}, defined c -> leaf c ->
                       sle Sh (st s c a) -> 
                       Transition s {|
                                    dt := dt s;
                                    ch := ch s;
                                    st := st s;
                                    dirSt := dirSt s;
                                    wt := wt s;
                                    wtS := wtS s;
                                    dirWt := dirWt s;
                                    dirWtS := dirWtS s
                                  |}
| StoreReq: forall {c a d}, defined c -> leaf c ->
                        (st s c a = Mo) ->
                        Transition s {|
                                     dt := fun t w => match decTree t c with
                                                      | left _ => match decAddr w a with
                                                                    | left _ => d
                                                                    | right _ => dt s t w
                                                                  end
                                                      | right _ => dt s t w
                                                      end;
                                     ch := ch s;
                                     st := st s;
                                     dirSt := dirSt s;
                                     wt := wt s;
                                     wtS := wtS s;
                                     dirWt := dirWt s;
                                     dirWtS := dirWtS s
                                   |}
| ChildSendReq: forall {p c}, defined p -> defined c -> parent c p ->
                              forall {x a}, slt (st s c a) x -> wt s c a = false ->
                                            Transition s {|
                                                         dt := dt s;
                                                         ch := fun t w z =>
                                                                 match t, decTree w c,
                                                                       decTree z p with
                                                                   | rch, left _, left _ =>
                                                                       (Build_BaseMesg
                                                                          (st s w a)
                                                                          x a (initData zero) rch)
                                                                         :: ch s t w z
                                                                   | _, _, _ => ch s t w z
                                                                 end;
                                                         st := st s;
                                                         dirSt := dirSt s;
                                                         wt := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ => true
                                                                            | _, _ => wt s t w
                                                                          end;
                                                         wtS := fun t w => match decTree t c, decAddr w a with
                                                                             | left _, left _ => x
                                                                             | _, _ => wtS s t w
                                                                           end;
                                                         dirWt := dirWt s;
                                                         dirWtS := dirWtS s
                                                       |}
| ParentRecvReq: forall {p c}, defined p -> defined c -> parent c p ->
                               ch s rch c p <> nil -> let r := last (ch s rch c p) dmy in
                                                        let fromR := fromB r in
                                                          let toR := toB r in
                                                            let a := addrB r in
                                                              sle toR (st s p a) ->
                               (forall i, defined i -> i <> c -> parent i p ->
                                          sle (dirSt s p i a)
                                              match toR with
                                                | Mo => In
                                                | Sh => Sh
                                                | In => Mo
                                              end) ->
                               dirWt s p c a = false ->
                               sle (dirSt s p c a) fromR ->
                               Transition s {| ch := fun t w z =>
                                                       match t with
                                                         | mch => match decTree w p,
                                                                        decTree z c with
                                                         | left _, left _ =>
                                                             (Build_BaseMesg
                                                                (dirSt s w z a) toR a (dt s w a) mch)
                                                               :: ch s t w z
                                                         | _, _ => ch s t w z
                                                                  end
                                                         | rch =>
                                                             match decTree w c,
                                                                   decTree z p with
                                                               | left _, left _ => removelast
                                                                                          (ch s t w z)
                                                               | _, _ => ch s t w z
                                                             end
                                                       end;
                                               dt := dt s;
                                               st := st s;
                                               dirSt := fun t w z => match decTree t p, decTree w c,
                                                                           decAddr z a with
                                                                       | left _, left _, left _ => toR
                                                                       | _, _, _ => dirSt s t w z
                                                                     end;
                                               wt := wt s;
                                               wtS := wtS s;
                                               dirWt := dirWt s;
                                               dirWtS := dirWtS s
                                            |}
| ChildRecvResp: forall {p c}, defined p -> defined c -> parent c p ->
                               ch s mch p c <> nil ->
                               let m := last (ch s mch p c) dmy in
                                 let fromM := fromB m in
                                   let toM := toB m in
                                     let a := addrB m in
                                       let d := dataBM m in
                                       type m = mch ->
                                         Transition s {| dt := fun t w =>
                                                                 match decTree t c,
                                                                       decAddr w a with
                                                                   | left _, left _ =>
                                                                     match fromB m with
                                                                       | In => d
                                                                       | _ => dt s t w
                                                                     end
                                                                   | _, _ => dt s t w
                                                                 end;
                                                         ch := fun t w z =>
                                                                 match t, decTree w p,
                                                                       decTree z c with
                                                                   | mch, left _, left _ => removelast (ch s t w z)
                                                                   | _, _, _ => ch s t w z
                                                                 end;
                                                         st := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ => toM
                                                                            | _, _ => st s t w
                                                                          end;
                                                         dirSt := dirSt s;
                                                         wt := fun t w => match decTree t c, decAddr w a with
                                                                            | left _, left _ =>
                                                                                match decSle (wtS s t w) toM with
                                                                                  | true => false
                                                                                  | _ => wt s t w
                                                                                end
                                                                            | _, _ => wt s t w
                                                                          end;
                                                         wtS := wtS s;
                                                         dirWt := dirWt s;
                                                         dirWtS := dirWtS s
                                                      |}
| ParentSendReq: forall {p c}, defined p -> defined c -> parent c p ->
                               forall {x a}, slt x (dirSt s p c a) -> dirWt s p c a = false ->
                                             Transition s {|
                                                          dt := dt s;
                                                          ch := fun t w z =>
                                                                  match t, decTree w p,
                                                                        decTree z c with
                                                                    | mch, left _, left _ =>
                                                                        (Build_BaseMesg
                                                                           (dirSt s w z a)
                                                                           x a (initData zero) rch)
                                                                          :: ch s t w z
                                                                    | _, _, _ => ch s t w z
                                                                  end;
                                                          st := st s;
                                                          dirSt := dirSt s;
                                                          wt := wt s;
                                                          wtS := wtS s;
                                                          dirWt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a
                                                                                with
                                                                                  | left _, left _, left _ =>
                                                                                      true
                                                                                  | _, _, _ => dirWt s t w z
                                                                                end;
                                                          dirWtS := fun t w z => match decTree t p, decTree w c,
                                                                                       decAddr z a with
                                                                                   | left _, left _, left _ => x
                                                                                   | _, _, _ => dirWtS s t w z
                                                                                 end

                                                        |}
| ChildRecvReq: forall {p c}, defined p -> defined c -> parent c p ->
                              ch s mch p c <> nil ->
                              let r := last (ch s mch p c) dmy in
                                let fromR := fromB r in
                                  let toR := toB r in
                                    let a := addrB r in
                                      let d := dataBM r in
                                      type r = rch ->
                                        slt toR (st s c a) ->
                              (forall {i}, defined i -> parent i c -> sle (dirSt s c i a) toR) ->
                              Transition s {| ch := fun t w z =>
                                                      match t with
                                                        | mch =>
                                                          match decTree w c, decTree z p with
                                                            | left _, left _ =>
                                                              (Build_BaseMesg (st s w a) toR a
                                                                              (dt s w a) mch)
                                                                :: ch s t w z
                                                            | left _, _ => ch s t w z
                                                            | _, _ => match decTree w p,
                                                                           decTree z c with
                                                                       | left _, left _ =>
                                                                         removelast (ch s t w z)
                                                                       | _, _ => ch s t w z
                                                                     end
                                                          end
                                                        | _ => ch s t w z
                                                      end;
                                              dt := dt s;
                                              st := fun t w => match decTree t c, decAddr w a with
                                                                 | left _, left _ => toR
                                                                 | _, _ => st s t w
                                                               end;
                                              dirSt := dirSt s;
                                              wt := wt s;
                                              wtS := wtS s;
                                              dirWt := dirWt s;
                                              dirWtS := dirWtS s
                                           |}
| ParentRecvResp: forall {p c}, defined p -> defined c -> parent c p ->
                                ch s mch c p <> nil ->
                                let m := last (ch s mch c p) dmy in
                                  let fromM := fromB m in
                                    let toM := toB m in
                                      let a := addrB m in
                                        let d := dataBM m in
                                        fromM = dirSt s p c a ->
                                          Transition s {| dt := fun t w => match decTree t p, decAddr w a with
                                                                             | left _, left _ =>
                                                                                 match fromB m with
                                                                                   | Mo => d
                                                                                   | _ => dt s t w
                                                                                 end
                                                                             | _, _ => dt s t w
                                                                           end;
                                                          ch := fun t w z =>
                                                                  match t, decTree w c,
                                                                        decTree z p with
                                                                    | mch, left _, left _ => removelast (ch s t w z)
                                                                    | _, _, _ => ch s t w z
                                                                  end;
                                                          st := st s;
                                                          dirSt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a with
                                                                                  | left _, left _, left _ => toM
                                                                                  | _, _, _ => dirSt s t w z
                                                                                end;
                                                          wt := wt s;
                                                          wtS := wtS s;
                                                          dirWt := fun t w z => match decTree t p, decTree w c,
                                                                                      decAddr z a with
                                                                                  | left _, left _, left _ =>
                                                                                      match decSle toM (dirWtS s t w z)
                                                                                      with
                                                                                        | true => false
                                                                                        | _ => dirWt s t w z
                                                                                      end
                                                                                  | _, _, _ => dirWt s t w z
                                                                                end;
                                                          dirWtS := dirWtS s
                                                       |}

| ChildVolResp: forall {p c}, defined p -> defined c -> parent c p ->
                              forall {x a},
                                slt x (st s c a) ->
                                (forall {i}, defined i -> parent i c -> sle (dirSt s c i a) x) ->
                                wt s c a = false ->
                                Transition s {| ch := fun t w z =>
                                                        match t, decTree w c,
                                                              decTree z p with
                                                          | mch, left _, left _ =>
                                                              (Build_BaseMesg
                                                                 (st s w a) x a (dt s w a) mch)
                                                                :: ch s t w z
                                                          | _, _, _ => ch s t w z
                                                        end;
                                                dt := dt s;
                                                st := fun t w => match decTree t c, decAddr w a with
                                                                   | left _, left _ => x
                                                                   | _, _ => st s t w
                                                                 end;
                                                dirSt := dirSt s;
                                                wt := wt s;
                                                wtS := wtS s;
                                                dirWt := dirWt s;
                                                dirWtS := dirWtS s
                                             |}
| ChildDropReq: forall {p c}, defined p -> defined c -> parent c p ->
                              ch s mch p c <> nil ->
                              let r := last (ch s mch p c) dmy in
                                let fromR := fromB r in
                                  let toR := toB r in
                                    let a := addrB r in
                                      let d := dataBM r in
                                      type r = rch ->
                                        sle (st s c a) toR ->
                              Transition s {| ch := fun t w z =>
                                                      match t, decTree w p,
                                                            decTree z c with
                                                        | mch, left _, left _ => removelast
                                                                                   (ch s t w z)
                                                        | _, _, _ => ch s t w z
                                                      end;
                                              dt := dt s;
                                              st := st s;
                                              dirSt := dirSt s;
                                              wt := wt s;
                                              wtS := wtS s;
                                              dirWt := dirWt s;
                                              dirWtS := dirWtS s
                                           |}.

Definition initGlobalState :=
  {| dt := fun t w => if (decTree t hier) then initData w else initData zero;
     ch := fun t w z => nil;
     st := fun t w => match decTree t hier with
                        | left _ => Mo
                        | right _ => In
                      end;
     dirSt := fun t w z => In;
     wt := fun t w => false;
     wtS := fun t w => In;
     dirWt := fun t w z => false;
     dirWtS := fun t w z => In
  |}.

Record Behavior := {
                    sys: Time -> GlobalState;
                    init: sys 0 = initGlobalState;
                    trans: forall t, Transition (sys t) (sys (S t))
                  }.

Definition CacheStream := Stream Transition.

Definition getCacheIo s s' (t: Transition s s') :=
  match t with
    | LoadReq c a _ _ _ => Some (a, c, initData zero, Ld, dt s c a)
    | StoreReq c a d _ _ _ => Some (a, c, d, St, initData zero)
    | _ => None
  end.

Module mkDataTypes <: DataTypes.

  Parameter cstm: CacheStream initGlobalState.

  Definition sys' (t: nat): GlobalState :=
    (fst (getStreamState t cstm)).

  Theorem init': sys' 0 = initGlobalState.
  Proof.
    unfold sys'.
    simpl.
    destruct cstm.
    reflexivity.
  Qed.

  Theorem trans' t: Transition (sys' t) (sys' (S t)).
  Proof.
    pose proof (stateNSndStateSnFst t cstm).
    pose proof (getStreamTransition t cstm).
    rewrite H in H0.
    assumption.
  Defined.
  Opaque sys' init' trans'.

  Definition oneBeh := Build_Behavior sys' init' trans'.

  Fixpoint labelCh t ch src dst :=
    match t with
      | 0 => nil
      | S t => match (trans oneBeh) t with
                 | ChildSendReq p c _ _ _ _ _ _ _ =>
                     match ch with
                       | rch =>
                           if (decTree src c)
                           then if (decTree dst p)
                                then t :: labelCh t ch src dst
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | mch => labelCh t ch src dst
                     end
                 | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                     match ch with
                       | rch =>
                           if (decTree dst p)
                           then if (decTree src c)
                                then removelast (labelCh t ch src dst)
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | mch =>
                           if (decTree dst c)
                           then if (decTree src p)
                                then t :: labelCh t ch src dst
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                     end
                 | ChildRecvResp p c _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           if (decTree src p)
                           then if (decTree dst c)
                                then removelast (labelCh t ch src dst)
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | rch => labelCh t ch src dst
                     end
                 | ParentSendReq p c _ _ _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           if (decTree src p)
                           then if (decTree dst c)
                                then t :: labelCh t ch src dst
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | rch => labelCh t ch src dst
                     end
                 | ChildRecvReq p c _ _ _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           match decTree dst p, decTree src c with
                             | left _, left _ => t :: labelCh t ch src dst
                             | left _, _ => labelCh t ch src dst
                             | _, _ =>
                                 match decTree dst c, decTree src p with
                                   | left _, left _ => 
                                       removelast (labelCh t ch src dst)
                                   | _, _ => labelCh t ch src dst
                                 end
                           end
                       | rch => labelCh t ch src dst
                     end
                 | ParentRecvResp p c _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           if (decTree src c)
                           then if (decTree dst p)
                                then removelast (labelCh t ch src dst)
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | rch => labelCh t ch src dst
                     end
                 | ChildVolResp p c _ _ _ _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           if (decTree src c)
                           then if (decTree dst p)
                                then t :: labelCh t ch src dst
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | rch => labelCh t ch src dst
                     end
                 | ChildDropReq p c _ _ _ _ _ _ =>
                     match ch with
                       | mch =>
                           if (decTree src p)
                           then if (decTree dst c)
                                then removelast (labelCh t ch src dst)
                                else labelCh t ch src dst
                           else labelCh t ch src dst
                       | rch => labelCh t ch src dst
                     end
                 | _ => labelCh t ch src dst
               end
    end.

  Definition state c a t := st ((sys oneBeh) t) c a.
  Definition dir p c a t := dirSt ((sys oneBeh) t) p c a.
  Definition wait c a t := wt ((sys oneBeh) t) c a.
  Definition waitS c a t := wtS ((sys oneBeh) t) c a.
  Definition dwait p c a t := dirWt ((sys oneBeh) t) p c a.
  Definition dwaitS p c a t := dirWtS ((sys oneBeh) t) p c a.
  Definition data c a t := dt ((sys oneBeh) t) c a.

  
  Definition mark chn src dst t m := match ((trans oneBeh) t) with
                                       | ChildSendReq p c _ _ _ x a _ _ =>
                                         c = src /\ p = dst /\ chn = rch /\
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = x /\ addr m = a /\
                                         dataM m = initData zero /\
                                         msgId m = t
                                       | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                                         p = src /\ c = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) rch c p) dmy in
                                         let a := addrB r in
                                         from m = (dirSt ((sys oneBeh) t) p c a) /\
                                         to m = toB r /\
                                         addr m = a /\
                                         dataM m = dt ((sys oneBeh) t) p a /\
                                         msgId m = t
                                       | ParentSendReq p c _ _ _ x a _ _ =>
                                         p = src /\ c = dst /\ chn = rch /\
                                         from m = (dirSt ((sys oneBeh) t) p c a) /\
                                         to m = x /\ addr m = a /\
                                         dataM m = initData zero /\
                                         msgId m = t
                                       | ChildRecvReq p c _ _ _ _ _ _ _ =>
                                         c = src /\ p = dst /\ chn = mch /\
                                         let r := last (ch ((sys oneBeh) t) mch p c) dmy in
                                         let a := addrB r in
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = toB r /\
                                         addr m = a /\
                                         dataM m = dt ((sys oneBeh) t) c a /\
                                         msgId m = t
                                       | ChildVolResp p c _ _ _ x a _ _ _ =>
                                         c = src /\ p = dst /\ chn = mch /\
                                         from m = (st ((sys oneBeh) t) c a) /\
                                         to m = x /\ addr m = a /\
                                         dataM m = dt (sys oneBeh t) c a /\
                                         msgId m = t
                                       | _ => False
                                     end.

  Definition recv chn src dst t m := match ((trans oneBeh) t) with
                                       | ParentRecvReq p c _ _ _ _ _ _ _ _ =>
                                         c = src /\ p = dst /\
                                         let r := last (ch ((sys oneBeh) t) rch c p) dmy in
                                         chn = type r /\
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t rch c p) 0
                                       | ChildRecvResp p c _ _ _ _ _ =>
                                         p = src /\ c = dst /\
                                         let r := last (ch ((sys oneBeh) t) mch p c) dmy in
                                         chn = type r /\
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch p c) 0
                                       | ChildRecvReq p c _ _ _ _ _ _ _ =>
                                         p = src /\ c = dst /\
                                         let r := last (ch ((sys oneBeh) t) mch p c) dmy in
                                         chn = type r /\
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch p c) 0
                                       | ParentRecvResp p c _ _ _ _ _ =>
                                         c = src /\ p = dst /\
                                         let r := last (ch ((sys oneBeh) t) mch c p) dmy in
                                         chn = type r /\
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch c p) 0
                                       | ChildDropReq p c _ _ _ _ _ _ =>
                                         p = src /\ c = dst /\
                                         let r := last (ch ((sys oneBeh) t) mch p c) dmy in
                                         chn = type r /\
                                         from m = fromB r /\
                                         to m = toB r /\ addr m = addrB r /\
                                         dataM m = dataBM r /\
                                         msgId m = last (labelCh t mch p c) 0
                                       | _ => False
                                     end.
  Definition markc t :=
    match (trans oneBeh t) with
      | ChildSendReq _ _ _ _ _ _ _ _ _ => rch
      | _ => mch
    end.

  Definition recvc t :=
    match (trans oneBeh t) with
      | ParentRecvReq _ _ _ _ _ _ _ _ _ _ => rch
      | _ => mch
    end.

  Definition invmark t :=
    match trans oneBeh t with
      | ChildSendReq _ _ _ _ _ _ _ _ _ => rch
      | ParentSendReq _ _ _ _ _ _ _ _ _ => rch
      | _ => mch
    end.

  Definition invrecv t :=
    match trans oneBeh t with
      | ParentRecvReq _ _ _ _ _ _ _ _ _ _ => rch
      | ChildRecvReq _ _ _ _ _ _ _ _ _ => rch
      | ChildDropReq _ _ _ _ _ _ _ _ => rch
      | _ => mch
    end.
  
  Definition send := mark.
  Definition proc := recv.
  Definition deq := recv.

  Definition getStreamCacheIo t := getCacheIo _ _ (trans oneBeh t).
End mkDataTypes.
