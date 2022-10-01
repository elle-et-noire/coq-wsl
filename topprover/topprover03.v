From mathcomp
  Require Import ssreflect div.
Require Import Nat Arith.

Definition task := forall n m, n < m \/ n = m \/ n > m.

(* TopProver umemasu *)
(* TopProver #6 *)

Lemma zeroLtN: forall n, 0 < S n.
Proof.
intros.
induction n.
by [].
auto.
Qed.

Lemma nGtZero: forall n, S n > 0.
Proof.
intros.
induction n.
by [].
auto.
Qed.

Theorem solution: task.
Proof.

unfold task.
(*intros.*)

induction n.
- induction m.
-- auto.
-- left. apply zeroLtN.
- induction m.
-- right; right. apply nGtZero.
-- destruct (IHn m).
--- left. apply lt_n_S. exact H.
-- destruct H.
--- right; left. apply eq_S. exact H.
--- right; right. apply gt_n_S. exact H.


Qed.