Require Import DataTypes List.

Set Implicit Arguments.

Variable Pc PState DeltaPState: Set.

Inductive HistElem :=
| Nmh: Pc -> DeltaPState -> HistElem
| Loadh: Pc -> Addr -> Data -> DeltaPState -> HistElem
| Storeh: Pc -> Addr -> Data -> HistElem.

Definition Hist := list HistElem.

Inductive DecodeElem :=
| Nm: DeltaPState -> DecodeElem
| Load: Addr -> DecodeElem
| Store: Addr -> Data -> DecodeElem.


Record ProcState :=
  { hist: Hist;
    getPc: Pc;
    state: PState
  }.

Variable updSt: PState -> DeltaPState -> PState.
Variable getLoadDelta: Pc -> PState -> Data -> DeltaPState.
Variable getDecodeElem: Pc -> PState -> (Pc * DecodeElem).

Inductive Simple: ProcState -> ProcState -> Set :=
| L1:
    forall st a nextPc delS v,
      getDecodeElem (getPc (st)) (state (st)) = (nextPc, Load a) ->
      getLoadDelta (getPc (st)) (state (st)) v = delS ->
      Simple
        st (Build_ProcState (Loadh (getPc (st)) a v delS :: (hist (st)))
                                   nextPc (updSt (state (st)) delS))
| S1:
    forall st a nextPc v,
      getDecodeElem (getPc (st)) (state (st)) = (nextPc, Store a v) ->
      Simple
        st (Build_ProcState (Storeh (getPc (st)) a v :: (hist (st)))
                                   nextPc (state (st)))
| N1:
    forall st nextPc delS,
      getDecodeElem (getPc (st)) (state (st)) = (nextPc, Nm delS) ->
      Simple
        st (Build_ProcState (Nmh (getPc (st)) delS :: (hist (st)))
                                   nextPc (updSt (state (st)) delS))
| Not1: forall st, Simple st st.

Definition SpecState := ProcState.

Inductive Speculative : SpecState -> SpecState -> Set :=
| L2:
    forall st a nextGetPc delS v,
      getDecodeElem (getPc (st)) (state (st)) = (nextGetPc, Load a) ->
      getLoadDelta (getPc (st)) (state (st)) v = delS ->
      Speculative
        st (Build_ProcState (Loadh (getPc (st)) a v delS :: (hist (st)))
                                   nextGetPc (updSt (state (st)) delS))
| L2':
    forall st a nextGetPc delS v,
      getDecodeElem (getPc (st)) (state (st)) = (nextGetPc, Load a) ->
      getLoadDelta (getPc (st)) (state (st)) v = delS ->
      Speculative
        st (Build_ProcState (Loadh (getPc (st)) a v delS :: (hist (st)))
                                   nextGetPc (updSt (state (st)) delS))
| S2:
    forall st a nextGetPc v,
      getDecodeElem (getPc (st)) (state (st)) = (nextGetPc, Store a v) ->
      Speculative
        st (Build_ProcState (Storeh (getPc (st)) a v :: (hist (st)))
                                   nextGetPc (state (st)))
| N2:
    forall st nextGetPc delS,
      getDecodeElem (getPc (st)) (state (st)) = (nextGetPc, Nm delS) ->
      Speculative
        st (Build_ProcState (Nmh (getPc (st)) delS :: (hist (st)))
                            nextGetPc (updSt (state (st)) delS))
| LBad:
    forall st (a: Addr) (v: Data),
      Speculative st st.

Definition Mem := Addr -> Data.

Definition upd A (st: Proc -> A) p v p' :=
  match decProc p p' with
    | left _ => v
    | _ => st p'
  end.

Definition updM A (st: Addr -> A) p v p' :=
  match decAddr p p' with
    | left _ => v
    | _ => st p'
  end.

Definition getMemSimple (c: Proc) p p' (ts: Simple p p') :=
  match ts with
    | L1 st a nextGetPc delS v _ _ => Some (a, c, initData zero, Ld, v)
    | S1 st a _ v _ => Some (a, c, v, St, initData zero)
    | N1 _ _ _ _ => None
    | Not1 _ => None
  end.

Inductive CorrectSystem: ((Proc -> ProcState) * (Addr -> Data)) ->
                         ((Proc -> ProcState) * (Addr -> Data)) -> Set :=
| Lod:
    forall p st m p' a
           (ts: Simple (st p) p'),
      getMemSimple p ts = Some (a, p, initData zero, Ld, m a) ->
      CorrectSystem (st, m) (upd st p p', m)
| Str:
    forall p st m p' a v
           (ts: Simple (st p) p'),
      getMemSimple p ts = Some (a, p, v, St, initData zero) ->
      CorrectSystem (st, updM m a v) (upd st p p', m)
| Others:
    forall p st m p'
           (ts: Simple (st p) p'),
      getMemSimple p ts = None ->
      CorrectSystem (st, m) (upd st p p', m).

Record State :=
  { mem: Addr -> Data;
    next: Addr -> Proc -> Index
  }.

Record Req := { desc: Desc;
                dataQ: Data
              }.

Record Resp := { addrR: Addr;
                 procR: Proc;
                 idx: Index;
                 datum: Data
               }.

Variable reqFn: Addr -> Proc -> Index -> Req.

Inductive AtomicTrans: State -> State -> Set :=
| AReq: forall s a c, AtomicTrans s (Build_State
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
| Idle: forall s, AtomicTrans s s.

Definition getMemSpec (c: Proc) p p' (ts: Speculative p p') :=
  match ts with
    | L2 st a nextgetPc delS v _ _ => Some (a, c, initData zero, Ld, v)
    | L2' st a nextGetPc delS v _ _ => Some (a, c, initData zero, Ld, v)
    | S2 st a _ v _ => Some (a, c, v, St, initData zero)
    | N2 _ _ _ _ => None
    | LBad _ a v => Some (a, c, initData zero, Ld, v)
  end.

Definition getMemAtomic p p' (ta: AtomicTrans p p') :=
  match ta with
    | AReq s a c => Some (a, c, dataQ (reqFn a c (next s a c)), desc (reqFn a c (next s a c)),
                          if desc (reqFn a c (next s a c))
                          then mem s a else initData zero)
    | Idle s => None
  end.

Inductive FullTrans: ((Proc -> SpecState) * State) -> ((Proc -> SpecState) * State) -> Set :=
| FTrans: forall c st s p' s'
                 (ts: Speculative (st c) p') (ta: AtomicTrans s s'),
                 getMemSpec c ts = getMemAtomic ta ->
                 FullTrans (st, s) (upd st c p', s').

Definition buildSimple s s' (ts: Speculative s s'): Simple s s' :=
  match ts with
    | L2 st a nextGetPc delS v p1 p2 => L1 st p1 p2
    | L2' st a nextGetPc delS v p1 p2 => L1 st p1 p2
    | S2 st a nextGetPc v p1 => S1 st p1
    | N2 st nextGetPc delS p1 => N1 st p1
    | LBad st a v => Not1 st
  end.
