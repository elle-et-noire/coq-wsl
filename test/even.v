From mathcomp Require Import ssreflect.
Require Import Setoid.

Fixpoint evenb (n: nat) :=
  match n with
  | O => true
  | S n' => negb (evenb n')
  end.
  
Fixpoint evenb' (n: nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb' n'
  end.
  
Lemma doubled_1 : not (exists k, 1 = 2 * k).
Proof.
  intros ([|], H); try discriminate.
  simpl in H.
  now rewrite <- plus_n_Sm in H.
Qed.

Lemma doubled_2 : forall (n: nat), (exists k, n = 2 * k) <-> (exists l, S (S n) = 2 * l).
Proof.
  split; intros (m, H).
  - exists (S m). rewrite H. simpl. now rewrite plus_n_Sm.
  - destruct m.
  -- simpl in H. inversion H.
  -- exists m. simpl in H. rewrite <-plus_n_Sm in H. now inversion H.
Qed. 

Theorem evenb'_bool_prop : 
  forall n, evenb' n = true <-> exists k, n = 2 * k.
Proof.
  fix evenb'_bool_prop 1.
  intro n; destruct n as [|[|n]].
  - split.
  -- intros. now exists 0.
  -- trivial.
  - split.
  -- now simpl.
  -- intros H. elim (doubled_1 H).
  - simpl. rewrite evenb'_bool_prop. apply doubled_2.
Qed. 

Lemma negneg : forall b, negb (negb b) = b.
Proof.
  intros b; case b; trivial.
Qed.

Theorem evenb_bool_prop :
  forall n, evenb n = true <-> exists k, n = 2 * k.
Proof.
  fix evenb_bool_prop 1.
  intros n; destruct n as [|[|n]].
  - split.
  -- intros. now exists 0.
  -- trivial.
  - split.
  -- now simpl.
  -- intros H. elim (doubled_1 H).
  - simpl. rewrite negneg evenb_bool_prop. simpl. apply doubled_2.
Qed.
