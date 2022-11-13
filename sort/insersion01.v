Require Import Arith List Sorting Permutation.
Import ListNotations.
From mathcomp Require Import ssreflect ssrnat ssrbool.

Fixpoint insert (i:nat) (l:list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <= h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l:list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
compute. reflexivity. Qed.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).



Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
   -- apply sorted_1.
   -- SearchPattern (forall n m, _ (n < m) -> _ (n <= m)). 
      case_eq (a <= x); intros H; apply sorted_cons; try apply sorted_1. 
      apply H. apply ltnW. by rewrite leqNgt ltnS H.
   -- case_eq (a <= x); intros H1. apply sorted_cons. apply H1.
    apply sorted_cons. apply H. apply S.
    move: IHS. unfold insert. case_eq (a <= y); intros H2 IHS.
    apply sorted_cons. apply /ltnW. by rewrite leqNgt ltnS H1. 
    apply IHS. fold insert. fold insert in IHS. 
    apply sorted_cons. apply H. apply IHS.
Qed.

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  induction l.
   -- apply sorted_nil.
   -- apply (insert_sorted a _ IHl).
Qed.

Lemma insert_permute: forall x l, Permutation (x :: l) (insert x l).
Proof.
  fix insert_permute 2.
  intros x l. destruct l as [|a l'].
   -- apply Permutation_refl.
   -- simpl. case_eq (x <= a); intros H.
   ---- apply Permutation_refl.
   ---- apply (@perm_trans _ _ (a :: x :: l') _).
    apply perm_swap. apply perm_skip. apply insert_permute.
  Qed.

Theorem sort_perm : forall l, Permutation l (sort l).
Proof.
  induction l.
   -- apply Permutation_refl.
   -- simpl. apply (@perm_trans _ _ (a :: sort l) _).
    apply perm_skip, IHl. 
    apply insert_permute.
Qed.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := 
  forall al, Permutation al (f al) /\ sorted (f al).

Theorem insertion_sort_correct : is_a_sorting_algorithm sort.
Proof.
  intros l. apply conj. apply sort_perm. apply sort_sorted. Qed.
  