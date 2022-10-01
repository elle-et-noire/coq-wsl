Require Import Utf8.

Set Implicit Arguments.

Definition feq A B (f g : A -> B) :=
  forall a, f a = g a.

Definition cancel A B (f: A -> B) (g: B -> A) :=
  forall a, g (f a) = a.

Definition injection A B (f: A -> B) :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition surjection A B (f: A -> B) :=
  forall b, exists a, f a = b.

Definition comp A B C (f: A -> B) (g: B -> C) (a: A) := g (f a).

Definition id {A} (a: A) := a.

Goal forall A B (f: A -> B), feq f f.
Proof. split. Qed.

Goal forall A B (f: A -> B), feq f f.
Proof. intros. unfold feq. reflexivity. Qed.

Goal forall A B (f g: A -> B), feq f g -> feq g f.
Proof. unfold feq. intros. rewrite H. reflexivity. Qed.

Goal forall A B (f g h: A -> B), feq f g -> feq g h -> feq f h.
Proof. congruence. Qed.

Goal forall A B (f g h: A -> B), feq f g -> feq g h -> feq f h.
Proof.
  unfold feq.
  intros.
  rewrite H.
  rewrite <-H0.
  reflexivity.
Qed.

Goal forall A B (f: A -> B), feq (fun a => f a) f.
Proof. split. Qed.

Goal forall A B (f: A -> B), feq (fun a => f a) f.
Proof. unfold feq. reflexivity. Qed.

Goal forall A B C D (f: A -> B) (g: B -> C) (h: C -> D), 
  comp (comp f g) h = comp f (comp g h).
Proof. split. Qed.

Goal forall A B (f: A -> B), feq (comp f id) f.
Proof. split. Qed.

Goal forall A B (f: A -> B), feq (comp id f) f.
Proof. split. Qed.

Goal forall A, injection (id: A -> A).
Proof.
  unfold injection. unfold id.
  intros. apply H.
Qed.

Goal forall A, surjection (id: A -> A).
Proof.
  unfold id. unfold surjection.
  intros.
  exists b.
  reflexivity.
Qed.

Goal forall A B (f: A -> B) (g: B -> A),
  cancel f g <-> feq (comp f g) id.
Proof.
  unfold cancel. unfold id. unfold feq. unfold comp.
  intros.
  split; intro H; apply H.
Qed.

Goal forall A (a: A), id a = a.
Proof. split. Qed.

Goal forall A B (f h: A -> B) (g: B -> A),
  cancel f g -> cancel g h -> feq f h.
Proof. congruence. Qed.

Goal forall A B (f h: A -> B) (g: B -> A),
  cancel f g -> cancel g h -> feq f h.
Proof.
  unfold cancel.
  unfold feq.
  intros.
  rewrite <-(H0 (f a)).
  apply f_equal.
  apply H.
Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  injection f -> injection g -> injection (comp f g).
Proof. firstorder. Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  injection f -> injection g -> injection (comp f g).
Proof.
  unfold injection.
  unfold comp.
  intros.
  apply H.
  apply H0.
  apply H1.
Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  surjection f -> surjection g -> surjection (comp f g).
Proof.
  unfold surjection.
  unfold comp.
  intros.
  destruct (H0 b).
  destruct (H x).
  exists x0.
  rewrite <-H1.
  rewrite H2.
  reflexivity.
Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  injection (comp f g) -> injection f.
Proof.
  unfold injection, comp.
  intros.
  apply H.
  rewrite H0.
  reflexivity.
Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  surjection (comp f g) -> surjection g.
Proof. firstorder. Qed.

Goal forall A B C (f: A -> B) (g: B -> C),
  surjection (comp f g) -> surjection g.
Proof.
  unfold surjection, comp.
  intros.
  destruct (H b).
  exists (f x).
  apply H0.
Qed.

Goal forall A B (f: A -> B) (g: B -> A),
  cancel f g -> injection f.
Proof. congruence. Qed.

Goal forall A B (f: A -> B) (g: B -> A),
  cancel f g -> injection f.
Proof.
  unfold cancel, injection.
  intros.
  rewrite <-(H a1), <-(H a2).
  apply f_equal, H0.
Qed.

Goal forall A B (f: A -> B) (g: B -> A),
  cancel f g -> surjection g.
Proof. firstorder. Qed.

Goal forall A B (f: A -> B) (g: B -> A),
  cancel f g -> surjection g.
Proof.
  unfold cancel, surjection.
  intros.
  exists (f b).
  apply H.
Qed.