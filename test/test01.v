From mathcomp
  Require Import ssreflect.

Section ModusPonens.
(* Variable X Y : Prop.

Hypothesis XtoY : X -> Y.
Hypothesis Xis : X.

Theorem MP : Y.
Proof.
 by apply XtoY.
Qed. *)

Theorem Chain : forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
intros.
by apply H0, H.
Show Proof.
Qed.

Print Chain.

Theorem Chain2 : forall X Y Z : Prop, (X -> Y -> Z) -> (X -> Y) -> X -> Z.
Proof.
  intros. apply: H. by[]. by apply H0.
Qed.

Print Chain2.

Theorem cap : forall X Y : Prop, X -> (X -> Y) -> Y.
Proof.
  move=> X Y Xis. by apply.
Qed.

Lemma HA2: forall (A B: Prop), (A -> B) -> ((A -> ~B) -> ~A).
Proof.
  intros A B AB AnotB Ais.
  absurd B; tauto.
Qed.