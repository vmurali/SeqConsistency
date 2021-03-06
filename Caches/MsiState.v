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


Inductive State := In | Sh | Mo.

Definition slt x y := match x, y with
                        | In, In => False
                        | Sh, Mo => True
                        | Sh, _ => False
                        | Mo, _ => False
                        | _, _ => True
                      end.
Definition sgt x y := slt y x.
Definition sle x y := match x, y with
                        | Sh, In => False
                        | Mo, In => False
                        | Mo, Sh => False
                        | _, _ => True
                      end.

Theorem sle_eq: forall {x y}, x = y -> sle x y.
Proof.
  intros x y x_eq_y. rewrite x_eq_y.
  unfold sle.
  destruct y; auto.
Qed.

Theorem slt_neq: forall {x y}, x = y -> ~ slt x y.
Proof.
  intros x y x_eq_y. rewrite x_eq_y. intros geez.
  unfold slt in geez.
  destruct y; auto.
Qed.

Theorem slt_neq': forall {x y}, slt x y -> x <> y.
Proof.
  unfold slt; destruct x; destruct y; auto; discriminate.
Qed.

Theorem slt_slti_false: forall {x y}, slt x y -> slt y x -> False.
Proof.
  intros x y slt1 slt2.
  unfold slt in *; destruct x in *; destruct y in *; auto.
Qed.

Theorem slt_slei_false: forall {x y}, slt x y -> sle y x -> False.
Proof.
  intros x y s1 s2.
  unfold slt in *; unfold sle in *; destruct x in *; destruct y in *; auto.
Qed.

Theorem not_slt_sle: forall {x y}, ~ slt x y -> sle y x.
Proof.
  intros x y noSlt.
  unfold sle; unfold slt in *;
                     destruct x; destruct y; auto.
Qed.

Theorem not_sle_slt: forall {x y}, ~ sle x y -> slt y x.
Proof.
  intros x y noSle.
  unfold sle in *; unfold slt in *;
         destruct x; destruct y; auto.
Qed.

Theorem slt_eq_slt_dec: forall {x y}, slt x y \/ x = y \/ slt y x.
Proof.
  intros x y.
  destruct x; destruct y; unfold slt; auto.
Qed.

Theorem slt_eq_sle: forall {x y}, sle x y = slt x y \/ x = y.
Proof.
  intros x y.
  unfold sle; unfold slt.
  destruct x; destruct y; auto.
Qed.

Theorem sle_sle_sle: forall {x y z}, sle x y -> sle y z -> sle x z.
Proof.
  intros x y z x_le_y y_le_z.
  unfold sle in *; destruct x; destruct y; destruct z; auto.
Qed.

Definition decSle x y := match x, y with
                           | Sh, In => false
                           | Mo, In => false
                           | Mo, Sh => false
                           | _, _ => true
                         end.

Definition decSle_sle : forall {x y}, decSle x y = true -> sle x y.
Proof.
  unfold decSle; unfold sle; intros x y; destruct x; destruct y; auto; discriminate.
Qed.
