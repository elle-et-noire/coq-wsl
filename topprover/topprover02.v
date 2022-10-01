Definition task := forall n m, n < m \/ n = m \/ n > m.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  elim n. elim m.
  right; left; reflexivity.
  intros. left.
  elim n0.
Qed.