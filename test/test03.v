From mathcomp Require Import all_ssreflect.

Lemma sample23_6 (m n : nat) : (m == n) = (n == m).
Proof.
  apply/idP/idP.
  (* m == n -> n == m *)
  - by move /eqP ->.
  (* n == m -> m == n *)
  - by move /eqP ->.
Qed.
