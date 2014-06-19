Require Import MsiState Tree BaseTree.

Export Tree.

Definition hier := getC nil bHier.
Opaque hier.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

Definition defined c := descendent c hier.

Definition Time := nat.

Inductive Desc := Ld | St.

Definition Index := nat.

Definition Cache := Tree.

Inductive ChannelType := mch | rch.

Theorem decCh: forall (x y: ChannelType), {x = y} + {x <> y}.
Proof.
  intros. decide equality.
Qed.

Parameter Data: Set.
Axiom decData: forall (d1 d2: Data), {d1 = d2} + {d1 <> d2}.

Definition Label := (Cache * Index)%type.
Theorem decLabel: forall (l1 l2: Label), {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1 l2.
  decide equality.
  decide equality.
  apply (decTree a c).
Qed.

Definition MLabel := Time.
Record Mesg := {
              from: State;
              to: State;
              addr: Addr;
              dataM: Data;
              msgId: MLabel
            }.

Record Req := { desc: Desc;
                dataQ: Data
              }.

Parameter reqFn: Addr -> Cache -> Index -> Req.
Parameter initData: Addr -> Data.

Module Type DataTypes.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter data: Cache -> Addr -> Time -> Data.

  Parameter wait: Cache -> Addr -> Time -> bool.
  Parameter waitS: Cache -> Addr -> Time -> State.
  Parameter dwait: Cache -> Cache -> Addr -> Time -> bool.
  Parameter dwaitS: Cache -> Cache -> Addr -> Time -> State.

  Parameter deqR: Addr -> Cache -> Index -> Time -> Prop.

  Parameter mark: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter send: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter recv: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter proc: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter deq: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
End DataTypes.



