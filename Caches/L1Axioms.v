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


Require Import Coq.Logic.Classical Caches.Rules Caches.DataTypes Caches.MsiState Caches.L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams Caches.DataTypes.

Module mkL1Axioms : L1Axioms mkDataTypes.
  Import mkDataTypes.

  Theorem deqLeaf: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> leaf c.
  Proof.
    intros; unfold getStreamCacheIo in *; unfold getCacheIo in *.
    destruct (trans oneBeh t);
    (match goal with
       | H: Some _ = Some _ |- _ => injection H; intros; subst; intuition
       | _ => discriminate
     end).
  Qed.

  Theorem deqDef: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) -> defined c.
  Proof.
    intros; unfold getStreamCacheIo in *; unfold getCacheIo in *.
    destruct (trans oneBeh t);
    (match goal with
       | H: Some _ = Some _ |- _ => injection H; intros; subst; intuition
       | _ => discriminate
     end).
  Qed.

  Theorem processDeq: forall a c d w ld t, getStreamCacheIo t = Some (a, c, d, w, ld) ->
                                           match w with
                                             | Ld => sle Sh (state c a t)
                                             | St => state c a t = Mo
                                           end.
  Proof.
    intros; unfold getStreamCacheIo in *; unfold getCacheIo in *.
    destruct (trans oneBeh t);
    (match goal with
       | H: Some _ = Some _ |- _ => injection H; intros; subst; intuition
       | _ => discriminate
     end).
  Qed.
End mkL1Axioms.
