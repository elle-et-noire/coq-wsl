Require Import Arith List Program.
Import ListNotations.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.


Fixpoint slide (i:nat) (l:list nat) :=
  match l with
  | [] => (i, [])
  | h :: t => if i < h then (fun p => (fst p, i :: snd p)) (slide h t)
              else (fun p => (fst p, h :: snd p)) (slide i t)
  end.

Lemma slide_hold_length : forall i l, length l = length (snd (slide i l)).
Proof.
  fix slide_hold_length 2.
  intros i. destruct l as [|a l']. simpl. done. simpl. 
  case_eq (i < a); intros H; simpl; apply f_equal; apply slide_hold_length.
Qed.

Program Fixpoint sort' (l1:list nat) (l2:list nat) {measure (length l2)} 
: (list nat) * (list nat):=
  match l2 with
  | [] => (l1, [])
  (* | h :: t => (fun p1 => (fun p2 => sort' ((snd p1) ++ [fst p2]) (snd p2))
    (slide (fst p1) t)) (slide h l1) *)
  | h :: t => sort' ((snd (slide h l1)) ++ [fst (slide (fst (slide h l1)) t)])
    (snd (slide (fst (slide h l1)) t))
  end.
Obligation 1.
simpl. pose (slide_hold_length (fst (slide h l1)) t) as e. rewrite -e. done.
Qed.

Definition sort (l:list nat) :=
  (fun p => fst p) (sort' [] l).

Goal sort [3;1;4;1;5;9;2;6;5;3;5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof. by compute. Qed.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma cons_sorted : forall h t, sorted (h :: t) -> sorted t.
Proof.
  intros h t S. inversion S. apply sorted_nil. apply H2.
Qed.

Lemma cons_cons_sorted : forall a h t, sorted (a :: h :: t) -> sorted (a :: t).
Proof.
  intros a h [|h2 t'] S. apply sorted_1. inversion S. inversion H3.
  apply sorted_cons. apply (leq_trans H1 H6). apply H8.
Qed.

Lemma slide_cons : forall a l, 
  sorted (a :: l) -> a :: l = (snd (slide a l)) ++ [fst (slide a l)].
Proof.
  fix slide_cons 2.
  intros a [|h t] S; simpl. done. case_eq (a < h); intros H; simpl.
  apply f_equal. inversion S. apply slide_cons, H4.
  inversion S.  pose (cons_cons_sorted a h t S) as S2.
  pose (slide_cons _ _ S2) as e. 
  assert (h :: (snd (slide a t)) ++  [(fst (slide a t))] 
  = h :: ((snd (slide a t)) ++ [fst (slide a t)])).
  apply app_comm_cons. rewrite -e. move: H H2. rewrite ltnNge. 
  move /eqP/eqP.  fold leq. intros H2 H9. fold leq in H2.
  assert (h <= a). apply H2. pose (conj H H9). 
  move: a0. move /andP=> a0. rewrite -eqn_leq in a0. 
  move:a0. move/eqP=> a0. by case a0.
Qed.

Lemma leq_cons_sorted : forall a h l, sorted (h :: l) -> a <= h ->
   sorted (a :: h :: l).
Proof.
  fix leq_cons_sorted 3.
  intros a h [|n l'] S. intros H. apply sorted_cons. apply H. apply sorted_1.
  intros H. apply sorted_cons. apply H. apply S.
Qed.

Lemma leq_all_cons_sorted : forall h a t, sorted (h :: t) -> h <= a -> 
  sorted (snd (slide a t) ++ [fst (slide a t)]) -> 
  sorted (h :: snd (slide a t) ++ [fst (slide a t)]).
Proof.
  fix leq_all_cons_sorted 3.
  intros h a [|i l']; simpl. intros S Hle.
  apply sorted_cons. apply Hle.
  intros S Hle. case_eq (a < i); intros H; simpl; intros S2.
  apply sorted_cons. apply Hle. apply S2. apply sorted_cons.
  inversion S. apply H2. apply S2.
Qed.

Lemma slide_sorted' : forall a l, sorted l -> 
  sorted ((snd (slide a l)) ++ [fst (slide a l)]).
Proof.
  fix slide_sorted' 2.
  intros a [|h t] S; simpl. apply sorted_1. case_eq (a < h); intros H; simpl.
  pose (cons_sorted _ _ S) as S2.
  pose (slide_sorted' h _ S2).
  apply leq_all_cons_sorted. assert (sorted (a :: h :: t)).
  apply sorted_cons. apply ltnW. apply H. apply S. 
  apply (cons_cons_sorted _ _ _ H0).
  apply ltnW, H. apply slide_sorted'. apply (cons_sorted _ _ S).
  apply leq_all_cons_sorted. apply S. move: H. rewrite ltnNge. 
  move/eqP/eqP => H.
  apply H. apply slide_sorted'. apply (cons_sorted _ _ S).
Qed.

Lemma app_cons_comm : forall (l1:list nat) n l2, 
  l1 ++ n :: l2 = (l1 ++ [n]) ++ l2.
Proof.
  induction l1. intros n l2. done.
  intros n l2. rewrite -app_comm_cons -app_comm_cons -app_comm_cons. 
  apply f_equal.
  apply IHl1.
Qed.

Lemma sorted_snoc : forall l n, sorted (l ++ [n]) -> sorted l.
Proof.
  induction l; intros n S. apply sorted_nil. rewrite -app_comm_cons in S.
  induction l. apply sorted_1. apply sorted_cons. inversion S. apply H1.
  inversion S. apply cons_sorted in S. apply (IHl _ S).
Qed.

Lemma app_sorted : forall l1 l2, sorted (l1 ++ l2) -> sorted l1.
Proof.
  fix app_sorted 2.
  intros l1. destruct l2.
  rewrite app_nil_r. apply.
  rewrite app_cons_comm. intros S. pose (app_sorted _ _ S) as S2.
  by apply sorted_snoc in S2.
Qed.
