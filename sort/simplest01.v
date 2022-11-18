Require Import Arith List Program Permutation.
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

  Lemma perm_top_bottom : forall {A:Type} (a:A) (l:list A),
    Permutation (a :: l) (l ++ [a]).
  Proof.
    move=> A a l. move:a. induction l. done.
    move=> a0. rewrite -app_comm_cons -IHl. apply perm_swap.
  Qed.
  
  Lemma assoc_app_cons : forall {A} (l1:list A) n l2, 
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

  (* Program Definition slide i (l:{l|sorted l})
    : {(a, l): nat * list nat | sorted (a :: l)} :=
    slide_kernel i l.
  Obligation 1.
    unfold slide_kernel.
  Check ({(a, l): nat * list nat | sorted (a :: l)}).
  Program Fixpoint slide (i:nat) (l: {l:list nat|sorted l}) {measure (length l)}
    : {(a, l): nat * list nat | sorted (a :: l)} :=
  match l with
  | [] => (i, [])
  | h :: t => 
    if i < h then 
      match slide h t with (h', t') => (h', i :: t') end
    else 
      match slide i t with (i', t') => (i', h :: t') end
  end.
  Next Obligation. apply sorted_1. Qed.
  Next Obligation. by apply sorted_tail in H. Qed.
  Next Obligation. by apply sorted_tail in H. Qed.
  Next Obligation.
    rewrite /=. case Hlt: (i < h).
    Eval compute in ((@sval) _ _ (exist _ nil sorted_nil)).
    Check slide_func_obligation_2.
    pose ((@sval) _ _
    (slide0 h
       (exist _ t (slide_func_obligation_2
             (exist _ (h :: t) H) slide0 h t Logic.eq_refl)) 
        (le_n (length t).+1))) as al.
    assert (let (a, l) := (let (h', t') :=
      al in (h', i :: t')) in sorted (a :: l)).
    rewrite 2!indep_prod /=. *)

  Section Sort.
    Lemma comm_slide_ind_head : forall i n l,
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
      move=> a l. move: a. induction l; move=> /= a0 S. done.
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
          rewrite app_comm_cons -(leq_simpl_sndslide Hc3) comm_slide_ind_head.
          apply IHl. done.
          by rewrite comm_slide_ind_head (leq_simpl_fstslide Hc3).
    Qed.
  End Sort.

  Section Perm.
    Lemma perm_slide : forall a l,
      Permutation (a :: l) (let (h, t) := slide a l in (t ++ [h])).
    Proof.
      move=> a l. move:a. induction l. done.
      move=> a0. destruct l; rewrite /=; case H: (a0 < a) => /=.
      - apply perm_skip, perm_skip, perm_nil.
      - apply perm_swap.
      - move:(IHl a). rewrite /= 5!indep_prod.
        case H2: (a < n) => /= IHl_a; apply perm_skip, IHl_a.
      - move:(IHl a0). rewrite /= 5!indep_prod.
        case H2: (a0 < n) => /= IHl_a0; 
        apply (perm_trans(l':= a :: a0 :: n :: l)); 
        try apply perm_swap; apply perm_skip, IHl_a0.
    Qed.
  End Perm.
End Slide.

Section Sort.
  Section Kernel.
    Variables l1 l2: list nat.
  Definition slidefb l1 h t :=
    match slide h l1 with (i, l1') =>
      match slide i t with (i', l2') => (l1' ++ [i'], l2') end
    end.

  Program Definition slidefb_coat (l1: {l|sorted l}) h t
    : {(l1', l2'): list nat * list nat | 
          sorted l1 /\ Permutation (l1 ++ h :: t) (l1' ++ l2')}
    := slidefb l1 h t.
  Obligation 1.
    rewrite indep_prod. apply conj. apply H.
    move:(perm_slide h l1) (perm_slide (fst (slide h l1)) t).
    rewrite /slidefb 4!indep_prod /=.
    pose (fst (slide h l1)) as i. pose (snd (slide h l1)) as l1'.
    fold i l1'. pose (fst (slide i t)) as i'. pose (snd (slide i t)) as l2'.
    fold i' l2'. move=> Hp1 Hp2.
    rewrite -app_assoc /= (perm_top_bottom i' l2') -Hp2.
    rewrite (assoc_app_cons l1' i t) -Hp1 (perm_top_bottom h l1) -app_assoc /=.
    apply Permutation_refl.
  Qed.

  Program Fixpoint sort_kernel (l1: {l | sorted l}) l2 {measure (length l2)}
    : {(l1', l2') : list nat * list nat | sorted l1' /\ Permutation (l1 ++ l2) (l1' ++ l2')} :=
    match l2 with
    | [] => (l1, [])
    | h :: t => match slidefb_coat l1 h t with
      (l1', l2') => sort_kernel l1' l2' end
    end.
  Next Obligation.
    move: (sorted_slide_snoc_geqind h l1 (fst (slide (fst (slide h l1)) t)) H).
    rewrite /slidefb 2!indep_prod in Heq_anonymous. inversion Heq_anonymous.
    rewrite indep_prod. apply. apply index_leq_fstslide.
  Qed.
  Next Obligation.
    rewrite /slidefb 2!indep_prod in Heq_anonymous. inversion Heq_anonymous.
    by rewrite -slide_hold_length.
  Qed.
  Next Obligation.
  pose (sort_kernel_func_obligation_2
    (exist _ l1 H) 
    (h :: t) sort_kernel h t Logic.eq_refl l1' l2' Heq_anonymous) as Sl1'.
  pose (sort_kernel_func_obligation_3
    (exist _ l1 H) 
    (h :: t) sort_kernel h t Logic.eq_refl l1' l2' Heq_anonymous) as Hlt.
  (* pose ((@sval) _ _ (sort_kernel (exist _ _ Sl1') l2' Hlt)) as l1l2. *)
  pose (sort_kernel (exist _ l1' Sl1') l2' Hlt) as l1sl2.
  (* Check (l1sl2 : { (l1'0, l2'0) : list nat * list nat |
    sorted l1'0 /\
    Permutation (l1' ++ l2') (l1'0 ++ l2'0)}). *)
  pose ((@sval) _
    (fun anonymous : list nat * list nat =>
    let (l1'0, l2'0) := anonymous in
    sorted l1'0 /\ Permutation (l1' ++ l2') (l1'0 ++ l2'0))
    l1sl2) as l1l2.
  fold Sl1' Hlt l1sl2 l1l2.

  rewrite indep_prod. apply conj.
  move: (proj2_sig l1sl2). rewrite /= !indep_prod /= => Sl1.
  apply Sl1.
  move: (proj2_sig l1sl2). rewrite /= !indep_prod /= => S_P.
  rewrite -(proj2 S_P). case Heq_anonymous.

  Check slidefb_coat_obligation_1.
  apply slidefb_coat_obligation_1.
  move:(perm_slide h l1) (perm_slide (fst (slide h l1)) t).
    rewrite /slidefb 4!indep_prod /=.
    pose (fst (slide h l1)) as i. pose (snd (slide h l1)) as l1'.
    fold i l1'. pose (fst (slide i t)) as i'. pose (snd (slide i t)) as l2'.
    fold i' l2'. move=> Hp1 Hp2.
    rewrite -app_assoc /= (perm_top_bottom i' l2') -Hp2.
    rewrite (assoc_app_cons l1' i t) -Hp1 (perm_top_bottom h l1) -app_assoc /=.
    apply Permutation_refl.

  
  

  
    pose (sort_kernel_func_obligation_2
    (exist _ l1 H) 
    (h :: t) sort_kernel h t Logic.eq_refl l1' l2' Heq_anonymous) as Sl1'.
    pose (sort_kernel_func_obligation_3
    (exist _ l1 H) 
    (h :: t) sort_kernel h t Logic.eq_refl l1' l2' Heq_anonymous) as Hlt.
    pose ((@sval) _ _ (sort_kernel (exist _ _ Sl1') l2' Hlt)) as l1l2.
    
    assert (let (l1'0, l2'0) := l1l2 in
      sorted l1'0 /\ Permutation (l1 ++ h :: t) (l1'0 ++ l2'0)).
    rewrite indep_prod. apply conj.


  Definition sort (l:list nat) := (proj1_sig (fst (sort_kernel (exist _ nil sorted_nil) l))).
  
  Goal sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
  Proof. by compute. Qed.
End Sort.
