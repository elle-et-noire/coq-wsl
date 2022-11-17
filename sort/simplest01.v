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
  fix slide_hold_length 2. move=> i [| a l'] /=. done.
  case H : (i < a); rewrite snd_destr_comm /=; apply f_equal, slide_hold_length.
Qed.


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

Lemma leq_all_cons_sorted' : forall a i l, 
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
  rewrite -(indep_prod _ _ _ (fun w1 w2 => _ :: w2 ++ [w1])); apply leq_all_cons_sorted'.
   - apply (cons_cons_sorted _ h _), (fun Hw => sorted_cons _ _ _ Hw S), ltnW, H.  
   - apply ltnW, H.
   - apply slide_sorted', (cons_sorted _ _ S).
   - apply S.
   - move:H. rewrite ltnNge. by move/eqP/eqP.
   - apply slide_sorted', (cons_sorted _ _ S).
Qed.

Corollary leq_all_cons_sorted : forall a i l, 
  sorted (a :: l) -> a <= i -> 
  sorted (let (h, t) := slide i l in a :: t ++ [h]).
Proof.
  move=> a i l S Hle. apply leq_all_cons_sorted'. apply S. apply Hle.
  apply slide_sorted'. apply (cons_sorted _ _ S).
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
  move => l1 [|n l2]. by rewrite app_nil_r.
  rewrite app_cons_comm => S. pose (app_sorted _ _ S) as S2.
  by apply sorted_snoc in S2.
Qed.

Corollary leq_all_cons_sorted_snd : forall a i l,
  sorted (a :: l) -> a <= i -> sorted (a :: snd (slide i l)).
Proof.
  move=> a i l S Hle. move: (leq_all_cons_sorted _ _ _ S Hle).
  rewrite indep_prod app_comm_cons. apply app_sorted.
Qed.

Lemma sorted_trans_cons_cons : forall l a b,
  sorted (l ++ [a]) -> sorted (a :: [b]) -> sorted (l ++ [a] ++ [b]).
Proof.
  induction l. done. induction l. move=> /= a0 b S1 S2.
  apply sorted_cons. inversion S1. apply H1. apply S2.
  move:IHl IHl0 => /= IHl IHl0 a1 b S1 S2. apply sorted_cons. inversion S1.
  apply H1. inversion S1. apply IHl. apply H3. apply S2.
Qed.

Lemma sorted_trans_cons: forall a h t l3,
  sorted (a :: h :: t) -> sorted (h :: t ++ l3) -> sorted (a :: h :: t ++ l3).
Proof.
  move=> /= a h t l3 S1 S2. apply sorted_cons. inversion S1. apply H1.
  apply S2.
Qed.

Lemma sorted_trans_app_app: forall l1 h t l3,
  sorted (l1 ++ h :: t) -> sorted (h :: t ++ l3) -> sorted (l1 ++ h :: t ++ l3).
Proof.
  induction l1. done.
  destruct l1. apply sorted_trans_cons.
  move:IHl1 => /= IHl1 h t l3 S1 S2. inversion S1.
  apply sorted_cons. apply H1. apply IHl1. 
  apply H3. apply S2.
Qed. 


Lemma slide_sorted : forall a l, sorted l -> sorted (snd (slide a l)).
Proof. 
  intros a l S. pose (slide_sorted' a _ S) as S2. move:S2.
  rewrite indep_prod. apply app_sorted.
Qed.

Lemma slide_leq : forall i l, i <= fst (slide i l).
Proof.
  fix slide_leq 2.
  move => i [|h t] => /=. done. case H: (i < h); rewrite indep_prod /=.
  apply (leq_trans (n := h)). apply ltnW, H. apply slide_leq.
  apply slide_leq.
Qed.

Lemma slide_geq_sorted : forall i l j, sorted l ->
  let (i', l') := slide i l in (i' <= j -> sorted (l' ++ [j])).
Proof.
  move => i l j. rewrite indep_prod. move: l i j. induction l.
  move=> i j S Hle; apply sorted_1. move: a.
  move=> a i j S /=. 
  rewrite 2! indep_prod. 
  destruct l; case H: (i < a) => /= Hle.
   - apply sorted_cons. apply (leq_trans(n:=a)). apply ltnW, H. apply Hle. apply sorted_1.
   - apply sorted_cons. apply (leq_trans(n:=i)). move:H.
    rewrite ltnNge. move/eqP/eqP. done. apply Hle. apply sorted_1.
   - move:Hle. rewrite 2!indep_prod. case H2: (a < n) => /= Hle.
     - apply sorted_cons. apply ltnW, H. 
      rewrite app_comm_cons. 
      inversion S. assert (fst (slide a (n :: l)) = fst (slide n l)).
      { rewrite /=. case H2': (a < n); rewrite indep_prod /=. done. 
        rewrite H2' in H2. inversion H2. }
      rewrite -H6 in Hle.
      pose (IHl a j H5 Hle). assert (snd (slide a (n :: l)) = a :: snd (slide n l)).
      { rewrite /=. case H2': (a < n); rewrite indep_prod /=. done.
        rewrite H2' in H2. inversion H2. }
      rewrite -H7. apply s.
    - inversion S. move:IHl S. case (leq_lt _ _ H2 H3) => /= IHl S.
      apply sorted_cons. apply ltnW, H. inversion S. 
      move:(IHl a j H10). case H': (a < a). rewrite ltnn in H'.
      inversion H'. rewrite indep_prod /=. apply. apply Hle.
  - move:Hle. rewrite 2!indep_prod. case H2: (i < n) => /= Hle.
    - apply sorted_cons. move: H. rewrite ltnNge. move/eqP/eqP. done.
      inversion S. assert (fst (slide i (n :: l)) = fst (slide n l)).
      { rewrite /=. case H2': (i < n); rewrite indep_prod /=. done.
        rewrite H2' in H2. inversion H2. }
      assert (snd (slide i (n :: l)) = i :: snd (slide n l)).
      { rewrite /=. case H2': (i < n); rewrite indep_prod /=. done.
        rewrite H2' in H2. inversion H2. }
      rewrite app_comm_cons -H7. apply IHl. apply H5.
      rewrite H6. apply Hle.
    - apply sorted_cons. inversion S. apply H3.
      inversion S. assert (fst (slide i l) = fst (slide i (n :: l))).
      { rewrite /=. case H2': (i < n); rewrite indep_prod /=. rewrite H2' in H2.
        inversion H2. done. }
      assert (n :: snd (slide i l) = snd (slide i (n :: l))).
      { rewrite /=. case H2': (i < n); rewrite indep_prod /=. rewrite H2' in H2.
        inversion H2. done. }
      rewrite app_comm_cons H7. apply IHl. apply H5. rewrite -H6. apply Hle.
Qed.

Lemma nill :{l | sorted l}.
apply (exist _ nil sorted_nil). Qed.
Check nill.
Check (exist _ nil sorted_nil).

Definition slidefb l1 h t :=
  match slide h l1 with (i, l1') =>
    match slide i t with (i', l2') => (l1' ++ [i'], l2')
    end
  end.

Lemma sorted_sort'_fst : forall l1 h t, sorted l1 ->
  match slide h l1 with (i, l1') => match slide i t with
    (i', l2') => sorted (l1' ++ [i']) end end.
Proof.
  move=> l1 h t S. rewrite 2!indep_prod /=.
  move: (slide_geq_sorted h l1 (fst (slide (fst (slide h l1)) t)) S).
  rewrite indep_prod. apply. apply slide_leq.
Qed.

Lemma sorted_sort'_fst' : forall l1 h t, sorted l1 -> sorted (fst (slidefb l1 h t)).
Proof.
  unfold slidefb. 
  move=> l1 h t /=. assert (sorted l1 -> sorted 
  (let (i, l1') := slide h l1 in
   let (i', l2') := slide i t in l1' ++ [i'])).
  move:(sorted_sort'_fst l1 h t). 
   rewrite 4!indep_prod /=. apply.   
  move:H. rewrite 4!indep_prod /=. apply.
Qed.

(* Definition sort'_noyau (l1s: {l | sorted l}) h t: {l | sorted l} :=
  match l1s with exist l1 Sl1 => 
    exist _ (fst (slidefb l1 h t)) (sorted_sort'_fst' _ h t Sl1)
  end. *)

Program Definition sort'_noyau (l1s: {l | sorted l}) h t : {l | sorted l} * list nat :=
  (* match l1s with exist l1 Sl1 => slidefb l1 h t end. *)
  slidefb l1s h t.
Obligation 1.
apply sorted_sort'_fst', H. Qed.

Program Fixpoint sort' (l1s: {l | sorted l}) l2 {measure (length l2)} : {l | sorted l} * list nat :=
  match l2 with
  | [] => (l1s, [])
  | h :: t => match sort'_noyau l1s h t with
    (l1s', l2') => sort' l1s' l2' end
  end.
Obligation 1.
move:sort' => /= sort'. unfold slidefb. 
by rewrite 2!indep_prod /= -slide_hold_length.
Qed.

Definition sort (l:list nat) := (proj1_sig (fst (sort' (exist _ nil sorted_nil) l))).

Compute sort [3;1;4;1;5;9;2;6;5;3;5]. 
Compute slide 5 [1;4;7;9].  
Goal sort [3;1;4;1;5;9;2;6;5;3;5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof. by compute. Qed.

Lemma sort'_sorted : forall l1 l2, sorted l1 -> 
  sorted (fst (sort' l1 l2)).
Proof.
  move=> l1 l2. move:l1. induction l2.
  move=> l1 S. apply S.
  move=> l1 S. unfold sort'.  unfold sort'_func. rewrite /=. indep_prod.  
fix sort'_sorted 2.

  move=> 
  intros l1. destruct l2. intros S.  simpl. apply S.
  intros S. 
  unfold sort', sort'_func. apply slide_sorted. simpl. snd. simpl. 
  Print sort'_func.

