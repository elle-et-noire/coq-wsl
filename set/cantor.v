(* https://www.youtube.com/watch?v=3ZHacSgSj0Q *)

Set Implicit Arguments.
Unset Strict Implicit.

Definition surjective (X Y : Type) (f: X -> Y): Prop :=
  forall y, exists x, f x = y.
  
Theorem Cantor : forall (X:Prop), not (exists f: X -> X -> Prop, surjective f).
Proof.
  intros X [f A].
  pose (g := fun x => not (f x x)).
  destruct (A g) as [x B].
  assert (C: g x <-> f x x).
  {
    rewrite B. tauto.
  }
  unfold g in C. tauto.
Qed.
