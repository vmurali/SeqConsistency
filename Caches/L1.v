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


Require Import Caches.DataTypes Omega Coq.Logic.Classical Caches.MsiState.

Set Implicit Arguments.

Module Type L1Axioms (dt: DataTypes).
  Import dt.
  Axiom deqLeaf: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> leaf c.
  Axiom deqDef: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> defined c.
  Axiom processDeq: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) ->
                                         match w with
                                           | Ld => sle Sh (state c a t)
                                           | St => state c a t = Mo
                                         end.
End L1Axioms.

Module Type L1Theorems (dt: DataTypes) (l1A: L1Axioms dt).
  Import dt l1A.
  Parameter latestValue:
  forall a c t,
    defined c ->
    leaf c ->
    sle Sh (state c a t) ->
    (data c a t = initData a /\
     forall {ti}, 0 <= ti < t -> forall ci di ldi,
                                   ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)) \/
    (exists cb tb, tb < t /\ getStreamCacheIo tb = Some (a, cb, data c a t, St, initData zero) /\
      forall ti, tb < ti < t ->
                   forall ci di ldi,
                     ~ getStreamCacheIo ti = Some (a, ci, di, St, ldi)).

  Parameter uniqM:
  forall c a t,
    defined c -> leaf c ->
    state c a t = Mo -> forall {co}, defined co -> leaf co -> c <> co -> state co a t = In.

End L1Theorems.
