Require Import Arith List Program.
Import ListNotations.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.


Fixpoint slide (i:nat) (l:list nat) :=
  match l with
  | [] => (i, [])
  | h :: t => 
    if i < h then 
      match slide h t with (h', t') => (h', i :: t') end
    else 
      match slide i t with (i', t') => (i', h :: t') end
  end.

Lemma snd_destr_comm : forall i (al:nat * list nat), 
  snd (let (a, l) := al in (a, i :: l)) = i :: snd al.
Proof. move=> i [a l]; done. Qed.

Lemma slide_hold_length : forall i l, 
  length l = length (snd (slide i l)).
Proof.
  fix slide_hold_length 2. move=> i [| a l']; rewrite /=. done.
  case H : (i < a); rewrite snd_destr_comm /=; apply f_equal, slide_hold_length.
Qed.

Program Fixpoint sort' (l1:list nat) (l2:list nat) {measure (length l2)} 
: (list nat) * (list nat):=
  match l2 with
  | [] => (l1, [])
  | h :: t => match slide h l1 with
      (i, l1') => match slide i t with
        (i', l2') => sort' (l1' ++ [i']) l2'
      end
    end
  end.
Obligation 1.
rewrite /=. assert (l2' = snd (slide i t)). by rewrite -Heq_anonymous.
by rewrite H -slide_hold_length.
Qed.

Definition sort (l:list nat) := fst (sort' [] l).

Compute sort [3;1;4;1;5;9;2;6;5;3;5]. 
Compute slide 5 [1;4;7;9].  
Goal sort [3;1;4;1;5;9;2;6;5;3;5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof. by compute. Qed.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma cons_sorted : forall h t, sorted (h :: t) -> sorted t.
Proof. intros h t S; inversion S; [apply sorted_nil | apply H2]. Qed.

Lemma cons_cons_sorted : forall a h t, sorted (a :: h :: t) -> sorted (a :: t).
Proof.
  intros a h [|h2 t'] S. apply sorted_1. inversion S. inversion H3.
  apply (sorted_cons _ _ _ (leq_trans H1 H6) H8).
Qed.

Lemma leq_lt : forall n m, (n < m) = false -> n <= m -> n = m.
Proof. 
  move=> n m. rewrite ltnNge. move/eqP/eqP => Nlt Hle.
  assert (m <= n) as Hge. { apply Nlt. }
  move: (conj Hle Hge). move/andP. rewrite -eqn_leq. by move/eqP.
Qed.

Lemma indep_prod : forall (A B C:Type) (f:A -> B -> C) (ab:A*B),
  (let (a, b) := ab in (f a b)) = f (fst ab) (snd ab).
Proof. intuition. Qed.

Lemma slide_cons : forall a l, 
  sorted (a :: l) -> a :: l = (let (a', l') := slide a l in (l' ++ [a'])).
Proof.
  fix slide_cons 2.
  intros a [|h t] S; rewrite /=. done. 
  rewrite 3!indep_prod. case H: (a < h) => /=.
   - apply f_equal. inversion S. 
    by rewrite (slide_cons _ _ H4) indep_prod.
   - inversion S. case (leq_lt _ _ H H2). apply f_equal.
    rewrite slide_cons. by rewrite indep_prod. apply (cons_cons_sorted _ _ _ S).
Qed.

Lemma leq_cons_sorted : forall a h l, 
  sorted (h :: l) -> a <= h -> sorted (a :: h :: l).
Proof. move=> a h [|n l'] S H; apply sorted_cons; [apply H|apply sorted_1|apply H|apply S]. Qed.

Lemma leq_all_cons_sorted : forall a i l, 
  sorted (a :: l) -> a <= i -> 
  sorted (let (h, t) := slide i l in t ++ [h]) ->
  sorted (let (h, t) := slide i l in a :: t ++ [h]).
Proof.
  move=> a i [|h t] S Hle /=.
   - apply sorted_cons, Hle.
   - rewrite 4!indep_prod; case H: (i < h) => S2 /=.
    apply (sorted_cons _ _ _ Hle), S2.
    inversion S. apply (sorted_cons _ _ _ H2 S2).
Qed.

Lemma slide_sorted' : forall a l, sorted l -> 
  sorted (let (h, t) := slide a l in t ++ [h]).
Proof.
  fix slide_sorted' 2.
  move=> a [|h t] S /=. apply sorted_1. case H: (a < h); rewrite 2!indep_prod /=;
  rewrite -(indep_prod _ _ _ (fun w1 w2 => _ :: w2 ++ [w1])); apply leq_all_cons_sorted.
   - apply (cons_cons_sorted _ h _), (leq_cons_sorted _ _ _ S), ltnW, H.  
   - apply ltnW, H.
   - apply slide_sorted', (cons_sorted _ _ S).
   - apply S.
   - move:H. rewrite ltnNge. by move/eqP/eqP.
   - apply slide_sorted', (cons_sorted _ _ S).
Qed. 

Lemma app_cons_comm : forall A (l1:list A) n l2, 
  l1 ++ n :: l2 = (l1 ++ [n]) ++ l2.
Proof. induction l1; by [|move=>n l2; rewrite -3!app_comm_cons IHl1]. Qed.

Lemma sorted_snoc : forall l n, sorted (l ++ [n]) -> sorted l.
Proof.
  induction l; intros n S. apply sorted_nil. rewrite -app_comm_cons in S.
  induction l. apply sorted_1. inversion S. apply sorted_cons. apply H1.
  apply cons_sorted in S. apply (IHl _ S).
Qed.

Lemma app_sorted : forall l1 l2, sorted (l1 ++ l2) -> sorted l1.
Proof.
  fix app_sorted 2.
  move => l1 [|n l2].
  (* intros l1. destruct l2. *)
  by rewrite app_nil_r.
  rewrite app_cons_comm => S. pose (app_sorted _ _ S) as S2.
  by apply sorted_snoc in S2.
Qed.

Lemma slide_sorted : forall a l, sorted l -> sorted (snd (slide a l)).
Proof. 
  intros a l S. pose (slide_sorted' a _ S) as S2. move:S2.
  rewrite indep_prod. apply app_sorted.
Qed.

(* Lemma sort'_sorted : forall l1 l2, sorted l1 -> sorted (fst (sort' l1 l2)).
Proof.
  fix sort'_sorted 2.
  intros l1. destruct l2. intros S.  simpl. apply S.
  intros S. 
  unfold sort', sort'_func. apply slide_sorted. simpl. snd. simpl. 
  Print sort'_func. *)

