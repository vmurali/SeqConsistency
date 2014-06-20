Require Import Coq.Logic.Classical Rules DataTypes MsiState L1 Omega Coq.Relations.Relation_Operators Coq.Lists.Streams DataTypes.

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