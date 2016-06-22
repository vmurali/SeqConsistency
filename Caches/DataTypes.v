(* Copyright (c) 2015 Muralidaran Vijayaraghavan vmurali@csail.mit.edu *)


(* Permission is hereby granted, free of charge, to any person obtaining *)
(* a copy of this software and associated documentation files (the *)
(* "Software"), to deal in the Software without restriction, including *)
(* without limitation the rights to use, copy, modify, merge, publish, *)
(* distribute, sublicense, and/or sell copies of the Software, and to *)
(* permit persons to whom the Software is furnished to do so, subject to *)
(* the following conditions: *)

(* The above copyright notice and this permission notice shall be *)
(* included in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE *)
(* LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION *)
(* OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION *)
(* WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. *)


Require Import SeqConsistency.DataTypes Caches.MsiState Caches.Tree Caches.BaseTree.
Export SeqConsistency.DataTypes.

Export Caches.Tree.

Definition hier := getC nil bHier.
Opaque hier.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

Definition defined c := descendent c hier.

Definition Time := nat.

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

Parameter initData: Addr -> Data.

Definition Proc := Cache.

Module Type DataTypes.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter data: Cache -> Addr -> Time -> Data.

  Parameter wait: Cache -> Addr -> Time -> bool.
  Parameter waitS: Cache -> Addr -> Time -> State.
  Parameter dwait: Cache -> Cache -> Addr -> Time -> bool.
  Parameter dwaitS: Cache -> Cache -> Addr -> Time -> State.

  Parameter mark: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter send: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter recv: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter proc: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.
  Parameter deq: ChannelType -> Cache -> Cache -> Time -> Mesg -> Prop.

  Parameter getStreamCacheIo: Time -> option (Addr * Cache * Data * Desc * Data).
End DataTypes.



