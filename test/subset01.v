(* http://adam.chlipala.net/cpdt/html/Subset.html *)

From mathcomp Require Import all_ssreflect.
Print Nat.pred.

Lemma zgtz: 0 > 0 -> False.
Proof. done. Qed.

Definition pred_strong1 {n: nat}: n > 0 -> nat :=
  match n with
  | O => fun (pf: 0 > 0) => match zgtz pf with end
  | S n' => fun _ => n'
  end.

Lemma two_gt0: 2 > 0.
Proof. done. Qed.

Eval compute in pred_strong1 two_gt0.

Print sig.
Locate "{ _ : _ | _ }".

Definition pred_strong2 (s: {n: nat | n > 0}): nat :=
  match s with
  | exist O pf => match zgtz pf with end
  | exist (S n') _ => n'
  end.
Eval compute in pred_strong2 (exist _ 2 two_gt0).