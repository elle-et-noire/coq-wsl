Require Import Arith.
Theorem restricted_excluded_middle
  : forall P b, (P <-> b = true) -> P \/ not P.
Proof.
  intros P b H.
  destruct b.
  - left. apply H. reflexivity.
  - right. intros F. apply H in F. inversion F.
Qed.

Theorem restricted_excluded_middle_eq
  : forall (n m: nat), n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (Nat.eqb n m)).
  symmetry.
  apply Nat.eqb_eq.
Qed.

