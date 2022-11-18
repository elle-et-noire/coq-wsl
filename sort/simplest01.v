Require Import Arith List Program.
Import ListNotations.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.


Section GeneralLemmas.
  Lemma indep_prod : forall (A B C:Type) (f:A -> B -> C) (ab:A*B),
    (let (a, b) := ab in (f a b)) = f (fst ab) (snd ab).
  Proof. intuition. Qed.

  Lemma leq_lt : forall {n m}, (n < m) = false -> n <= m -> n = m.
  Proof. 
    move=> n m. rewrite ltnNge. move/eqP/eqP => Nlt Hle.
    apply/eqP. rewrite eqn_leq. apply /andP; apply conj.
    apply Hle. apply Nlt.
  Qed.
  
  Lemma app_cons_comm : forall A (l1:list A) n l2, 
  l1 ++ n :: l2 = (l1 ++ [n]) ++ l2.
  Proof. induction l1; by [|move=>n l2; rewrite -3!app_comm_cons IHl1]. Qed.
End GeneralLemmas.

Section Sorted.
  Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_1 : forall x, sorted [x]
  | sorted_cons : forall {x y l},
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

  Lemma sorted_tail : forall {h t}, sorted (h :: t) -> sorted t.
  Proof. move=> h [|i l] S. apply sorted_nil. inversion S. apply H3. Qed.

  Lemma sorted_1_3toend : forall {a h t}, 
    sorted (a :: h :: t) -> sorted (a :: t).
  Proof.
    move=> a h [|h2 t'] S. apply sorted_1. inversion S. inversion H3.
    apply (sorted_cons (leq_trans H1 H6) H8).
  Qed.
(* 
  Lemma sorted_before_cons : forall l n, sorted (l ++ [n]) -> sorted l.
  Proof.
    induction l; intros n S. apply sorted_nil. rewrite -app_comm_cons in S.
    induction l. apply sorted_1. inversion S. apply sorted_cons. apply H1.
    apply sorted_tail in S. apply (IHl _ S).
  Qed.

  Lemma sorted_before_app : forall l1 l2, sorted (l1 ++ l2) -> sorted l1.
  Proof.
    move=> l1 l2. move:l1. induction l2; move=> l1. by rewrite app_nil_r.
    rewrite app_cons_comm => S. apply IHl2 in S.
    by apply sorted_before_cons in S.
  Qed. *)
End Sorted.

Section Slide.
  Fixpoint slide (i:nat) (l:list nat) :=
    match l with
    | [] => (i, [])
    | h :: t => 
      if i < h then 
        match slide h t with (h', t') => (h', i :: t') end
      else 
        match slide i t with (i', t') => (i', h :: t') end
    end.

  Lemma slide_cons_fst_comm : forall i n l,
    slide i (n :: l) = slide n (i :: l).
  Proof.
    move=> i n l. rewrite /= 2!indep_prod /=. 
    case H: (i < n); case H2: (n < i).
    - pose (ltn_geF H). apply ltnW in H2. by rewrite e in H2.
    - done.
    - done.
    - rewrite ltnNge in H2. move:H2. move/eqP/eqP => H2.
      by case (leq_lt H H2).
  Qed.

  Lemma slide_hold_length : forall i l, 
    length l = length (snd (slide i l)).
  Proof.
    move=> i l. move:i. induction l. done.
    move=> i. rewrite /= 2!indep_prod. 
    case H : (i < a) => /=; apply f_equal, IHl.
  Qed.

  Lemma slide_hold_sortedlist : forall a l, sorted (a :: l) ->
    a :: l = (let (a', l') := slide a l in (l' ++ [a'])).
  Proof.
    move=>a l. move: a. induction l; move=> /= a0 S. done.
    rewrite 3!indep_prod /=. case H: (a0 < a) => /=.
    - apply f_equal. inversion S.
      by rewrite (IHl _ H4) indep_prod.
    - inversion S. case (leq_lt H H2). apply f_equal.
      rewrite IHl. by rewrite indep_prod.
      apply (sorted_1_3toend S).
  Qed.

  Lemma index_leq_fstslide : forall i l, i <= fst (slide i l).
  Proof.
    fix index_leq_fstslide 2.
    move => i [|h t] => /=. done. 
    case H: (i < h); rewrite indep_prod /=.
    - apply (leq_trans (n := h)). apply ltnW, H. apply index_leq_fstslide.
    - apply index_leq_fstslide.
  Qed.

  Lemma leq_simpl_fstslide : forall {a n l}, a <= n ->
    fst (slide a (n :: l)) = fst (slide n l).
  Proof.
    move=> a n l Hle => /=. case H: (a < n); rewrite indep_prod /=.
    done. by case (leq_lt H Hle).
  Qed.

  Lemma leq_simpl_sndslide : forall {a n l}, a <= n ->
    snd (slide a (n :: l)) = a :: snd (slide n l).
  Proof.
    move=> a n l Hle => /=. case H: (a < n); rewrite indep_prod /=.
    done. by case (leq_lt H Hle).
  Qed.

  Lemma sorted_slide_snoc_geqind : forall i l j, sorted l ->
    let (i', l') := slide i l in (i' <= j -> sorted (l' ++ [j])).
  Proof.
    move=> i l j. rewrite indep_prod. move: l i j. induction l.
    move=> i j S Hle; apply sorted_1.
    move=> i j S /=. rewrite 2! indep_prod. 
    destruct l; rewrite /=.
    - case H: (i < a) => /= Hle; apply sorted_cons; try apply sorted_1.
      - apply (leq_trans(n:=a)). apply ltnW, H. apply Hle.
      - apply (leq_trans(n:=i)). move:H. rewrite ltnNge. 
        by move/eqP/eqP. apply Hle.
    - inversion S. case Hc: (i < a); [case Hc2: (a < n) | case Hc2: (i < n)]; 
      rewrite indep_prod /= => Hle.
      - apply sorted_cons. apply ltnW, Hc.
        rewrite app_comm_cons -(leq_simpl_sndslide H1).
        apply IHl. done. by rewrite (leq_simpl_fstslide H1).
      - move:IHl H3. case (leq_lt Hc2 H1) => IHl H3.
        apply sorted_cons. apply ltnW, Hc. 
        rewrite app_comm_cons -(leq_simpl_sndslide (leqnn _)).
        apply IHl. done. by rewrite (leq_simpl_fstslide (leqnn _)).
      - apply sorted_cons. move:Hc. rewrite ltnNge. by move/eqP/eqP.
        rewrite app_comm_cons -(leq_simpl_sndslide (ltnW Hc2)).
        apply IHl. done. 
        by rewrite (leq_simpl_fstslide (ltnW Hc2)).
      - apply sorted_cons. apply H1. assert (n <= i) as Hc3. 
        { move:Hc2. rewrite ltnNge. by move/eqP/eqP. }
        rewrite app_comm_cons -(leq_simpl_sndslide Hc3) slide_cons_fst_comm.
        apply IHl. done.
        by rewrite slide_cons_fst_comm (leq_simpl_fstslide Hc3).
  Qed.
End Slide.

Section Sort.
  Definition slidefb l1 h t :=
    match slide h l1 with (i, l1') =>
      match slide i t with (i', l2') => (l1' ++ [i'], l2') end
    end.

  Program Fixpoint sort_kernel (l1: {l | sorted l}) l2
      {measure (length l2)} : {l | sorted l} * list nat :=
    match l2 with
    | [] => (l1, [])
    | h :: t => match slidefb l1 h t with
      (l1s', l2') => sort_kernel l1s' l2' end
    end.
  Obligation 1.
    move: (sorted_slide_snoc_geqind h l1 (fst (slide (fst (slide h l1)) t)) H).
    rewrite /slidefb 2!indep_prod in Heq_anonymous. inversion Heq_anonymous.
    rewrite indep_prod. apply. apply index_leq_fstslide.
  Qed.
  Obligation 2.
    rewrite /slidefb 2!indep_prod in Heq_anonymous. inversion Heq_anonymous.
    by rewrite -slide_hold_length.
  Qed.

  Definition sort (l:list nat) := (proj1_sig (fst (sort_kernel (exist _ nil sorted_nil) l))).
  
  Goal sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
  Proof. by compute. Qed.
End Sort.
