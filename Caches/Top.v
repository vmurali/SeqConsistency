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


Require Import Caches.DataTypes Caches.L1 SeqConsistency.StoreAtomicity Caches.LatestValue Caches.Cache Caches.Channel Caches.Compatible
Caches.Rules Caches.ChannelAxiom Caches.L1Axioms Caches.CompatBehavior Caches.LatestValueAxioms Caches.BehaviorAxioms Caches.MsiState SeqConsistency.TransitionsNew.

Set Implicit Arguments.
  Module l1 := mkL1Axioms.
  Module ch' := mkChannel.
  Module ch := mkChannelPerAddr mkDataTypes ch'.
  Module comp := mkCompatBehavior ch.
  Module lv := mkLatestValueAxioms ch.
  Module ba := mkBehaviorAxioms.
  Module l1T := LatestValueTheorems mkDataTypes ch ba l1 comp lv.
    Import mkDataTypes l1 l1T lv.


  Theorem storeAtomicityLd':
    forall t a c d ld,
      getStreamCacheIo t = Some (a, c, d, Ld, ld) ->
      (ld = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi,
                                   ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)) \/
    (exists cb tb ldb, tb < t /\ getStreamCacheIo tb = Some (a, cb, ld, St, ldb) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi,
                     ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)).
  Proof.
    intros.
    pose proof (deqLeaf H) as lf.
    pose proof (deqDef H) as def.
    pose proof (latestValue a t def lf) as lv.
    pose proof (processDeq H) as sth.
    Opaque sle.
    simpl in *.
    pose proof (deqLdImpData def H) as [u1 u2].
    rewrite <- u2, u1 in *.
    specialize (lv sth).
    intuition.
    right.
    destruct H0 as [cb [tb rest]].
    exists cb, tb, (initData zero).
    assumption.
  Qed.

  Theorem storeAtomicitySt':
    forall t a c d ld,
      getStreamCacheIo t = Some (a, c, d, St, ld) ->
      ld = initData zero.
  Proof.
    intros.
    pose proof (deqLeaf H) as lf.
    pose proof (deqDef H) as def.
    pose proof (deqImpData def H) as [u1 u2].
    assumption.
  Qed.


  Theorem cacheIsStoreAtomic : StoreAtomicity zero initData cstm getCacheIo.
  Proof.
    assert  (forall (t: Time) (a : Addr) (c : Tree) (d ld : Data),
      getCacheIo _ _ (getStreamTransition cstm t) = Some (a, c, d, Ld, ld) ->
      ld = initData a /\
      (forall ti : nat,
       0 <= ti < t ->
       forall (ci : Tree) (di ldi : Data),
       getCacheIo _ _ (getStreamTransition cstm ti) <> Some (a, ci, di, St, ldi)) \/
      (exists (cb : Tree) (tb : nat) (ldb : Data),
         tb < t /\
         getCacheIo _ _ (getStreamTransition cstm tb) = Some (a, cb, ld, St, ldb) /\
         (forall ti : nat,
          tb < ti < t ->
          forall (ci : Tree) (di ldi : Data),
          getCacheIo _ _ (getStreamTransition cstm ti) <> Some (a, ci, di, St, ldi)))).
    intros.
    pose proof (@storeAtomicityLd' t a c d ld).
    destruct H0.
    pose proof (sameThing t).
    rewrite H in H0.
    assumption.
    left.
    constructor; intuition.
    pose proof (sameThing ti).
    rewrite <- H5 in H0.
    specialize (H2 ti (conj H3 H4) ci di ldi H0).
    intuition.
    right.
    destruct H0 as [cb [tb [ldb [cond [sth  rest]]]]].
    exists cb, tb, ldb.
    constructor.
    intuition.
    constructor.
    pose proof (sameThing tb).
    rewrite H0 in sth.
    assumption.
    unfold not; intros.
    specialize (rest ti H0 ci di ldi).
    pose proof (sameThing ti).
    rewrite H2 in rest.
    intuition.
    

    assert (great: forall t a c d ld,
      getCacheIo _ _ (getStreamTransition cstm t) = Some (a, c, d, St, ld) ->
      ld = initData zero).

    intros.

    pose proof (sameThing t).
    rewrite <- H1 in H0.
    pose proof (@storeAtomicitySt' t a c d ld H0).
    intuition.

    apply (Build_StoreAtomicity zero initData _ _ H great).
  Qed.
