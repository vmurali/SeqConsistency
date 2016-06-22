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


Require Import Caches.DataTypes List Caches.Tree Coq.Relations.Relation_Operators Omega Caches.BaseTree.

Module mkHierProperties (dt: DataTypes).
  Import dt.

  Theorem hasFork:
    forall {c1 c2},
      defined c1 -> defined c2 ->
      ~ descendent c1 c2 -> ~ descendent c2 c1 ->
      exists fork, defined fork /\
                           (exists d1, defined d1 /\ parent d1 fork /\ descendent c1 d1 /\ ~ descendent c2 d1) /\
                           (exists d2, defined d2 /\ parent d2 fork /\ ~ descendent c1 d2 /\ descendent c2 d2).
  Proof.
    unfold defined.
    pose proof @hasFork'.
    intros c1 c2 p1 p2 x1 x2.
    specialize (H c1 c2 x1 x2 hier p1 p2).
    firstorder.
  Qed.

  Theorem hierHasNoParent:
    forall {p}, defined p -> parent hier p -> False.
  Proof.
    intros p defP hier_p.
    pose proof (treeName2 defP) as prop.
    unfold treeNthName in prop.
    unfold parent in hier_p.
    destruct p.
    clear defP.
    assert (prop2: forall n, n < length l0 ->
                             match nth n l0 (C nil nil) with
                               | C x _ => x <> nil
                             end).
    intros n cond; specialize (prop n cond); destruct (nth n l0 (C nil nil)).
    unfold not; intros rew.
    rewrite rew in prop; discriminate.
    clear prop.
    induction l0.
    unfold In in hier_p.
    assumption.
    unfold In in hier_p.
    destruct hier_p as [a_eq_hier | hard].
    rewrite a_eq_hier in *.
    
    assert (z_lt_S: 0 < length (hier :: l0)) by (unfold length; omega).
    specialize (prop2 0 z_lt_S).
    unfold nth in prop2.
    pose proof (treeName1) as tn1.
    unfold hier in *.
    destruct hier.
    firstorder.
    specialize (IHl0 hard).
    assert (forall n, n < length l0 -> match nth n l0 (C nil nil) with
                                         | C x _ => x <> nil
                                       end).
    intros n n_lt_l0.
    specialize (prop2 (S n)).
    assert (S_n_lt_al0: S n < length (a :: l0)).
    unfold length. unfold length in n_lt_l0.
    omega.
    assert (nthEq: nth n l0 (C nil nil) = nth (S n) (a::l0) (C nil nil)).
    unfold nth.
    reflexivity.
    rewrite <- nthEq in prop2.
    firstorder.
    firstorder.
  Qed.
End mkHierProperties.
  
