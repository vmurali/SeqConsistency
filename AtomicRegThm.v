Set Implicit Arguments.

Require Import AtomicReg AtomicRegIfc StoreAtomicity DataTypes Transitions.

Section ForAddr.
  Variable reqFn: Addr -> Cache -> Index -> Req.
  Variable respFn: Time -> option Resp.

  Variable sa: StoreAtomicity reqFn respFn.

  Theorem atomicRegSimulateCaches n :
    exists (al: Stream (AtomicTrans reqFn) (Build_State (initData) (fun a t => 0))),
      getCacheIo reqFn respFn n = getStreamIo (@getTransIo reqFn ) n al.
  Proof.
    exists (buildAl reqFn respFn 0).
    About getRespEq.
    pose proof (getIoEq sa n) as e1.
    pose proof (ioEq sa n) as e2.
    rewrite <- e1 in e2.
    assumption.
  Qed.
End ForAddr.

Section InstantMemory.
  Variable reqFn: Addr -> Cache -> Index -> Req.

  Inductive InstantMem: (Addr -> Data) -> (Addr -> Data) -> Set :=
  | IReq: forall m a (p: Proc) d (w: Desc),
            InstantMem m (fun a' => 
                            if w
                            then m a'
                            else 
                              if decAddr a a'
                              then d
                              else m a')
  | IIdle: forall m, InstantMem m m.

  Theorem instSimulateAtomic:
    forall sa (sas: Stream TransA sa),
    exists sb (sbs: Stream TransB sb),
      forall n,
        getStreamIo getTransAIo n sas = getStreamIo getTransBIo n sbs.
