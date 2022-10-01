From mathcomp
  Require Import ssreflect ssrnat ssrbool.

Definition task := forall n m, (lt n m) \/ n = m \/ (gt n m).

Theorem solution: task.
Proof.
  unfold task.
  intros n.
  elim n. intros m. elim m.
  by right; left.
  intros. left. by apply /ltP. intros.
  elim m. by right; right; apply /ltP.
  intros. destruct (H n1).
  left. move: H1. move /ltP=> H1. by apply/ltP.
  destruct H1.
  right; left. by rewrite H1. 
  right; right. move: H1. move/ltP=> H1. by apply/ltP.
Qed.