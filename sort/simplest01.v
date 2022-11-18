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

Module Sort.
  Section Kernel.
    Context {lst1 lst2: list nat}.
    Definition SPL n _l1 _l2 := sorted _l1 /\ Permutation (lst1 ++ lst2) (_l1 ++ _l2) /\ length _l2 = n.
    Definition splpair n := {(_l1, _l2): list nat * list nat | SPL n _l1 _l2}.
    Definition sppair := {(_l1, _l2): list nat * list nat |
      sorted _l1 /\ Permutation (lst1 ++ lst2) (_l1 ++ _l2)}.
    Lemma sorted_fst_sppair : forall {n} {sp:splpair n}, sorted (fst (proj1_sig sp)).
    Proof. move=> n sp. destruct sp. destruct x. destruct y. apply s. Qed.
    Lemma perm_sppair_app : forall {n} {sp:splpair n}, 
      Permutation (lst1 ++ lst2) (fst (proj1_sig sp) ++ snd (proj1_sig sp)).
    Proof. move=> n sp. destruct sp. destruct x. destruct y as [s [p a]]. apply p. Qed.
    Lemma length_l2_n : forall {n} {sp:splpair n},
      length (snd (proj1_sig sp)) = n.
    Proof. move=> n sp. destruct sp. destruct x. destruct y as [s [p a]]. apply a. Qed.
    Definition l2_length {n} (sp:splpair n) := n.

    Definition slidefb l1 h t :=
      match slide h l1 with (i, l1') =>
        match slide i t with (i', l2') => (l1' ++ [i'], l2') end
      end.
    Lemma slidefb_shorten_l2 : forall l1 h t,
      length (snd (slidefb l1 h t)) = length t.
    Proof. move=> l1 h t. by rewrite /slidefb 2!indep_prod /= -slide_hold_length. Qed.

    Program Definition slidefb_coat {n} (l1ht:splpair n) : splpair (n - 1) :=
      match l1ht with (l1, l2) => 
        match l2 with 
        | h :: t => slidefb l1 h t
        | [] => (l1, l2)
        end
      end.
    Obligation 1.
      assert (l1 = fst (proj1_sig l1ht)) as El1. { by rewrite -Heq_l1ht. }
      assert (h :: t = snd (proj1_sig l1ht)) as Eht. { by rewrite -Heq_l1ht. }
      rewrite /slidefb 3!indep_prod /=. apply conj; try apply conj.
      - assert (sorted l1) as H. { rewrite El1. apply sorted_fst_sppair. }
        move: (sorted_slide_snoc_geqind h l1 (fst (slide (fst (slide h l1)) t)) H).
        rewrite indep_prod. apply. apply index_leq_fstslide.
      - move:(perm_slide h l1) (perm_slide (fst (slide h l1)) t).
        rewrite 2!indep_prod.
        pose (fst (slide h l1)) as i. pose (snd (slide h l1)) as l1'.
        fold i l1'. pose (fst (slide i t)) as i'. pose (snd (slide i t)) as l2'.
        fold i' l2'. move=> Hp1 Hp2.
        rewrite -app_assoc /= (perm_top_bottom i' l2') -Hp2.
        rewrite (assoc_app_cons l1' i t) -Hp1 (perm_top_bottom h l1) -app_assoc /=.
        rewrite Eht El1. apply perm_sppair_app.
      - rewrite -slide_hold_length.
        assert (length (h :: t) = n) as Elen. { rewrite Eht. apply length_l2_n. }
        rewrite /= in Elen. rewrite -Elen. by rewrite subn1 /=. 
    Qed.
    Obligation 2.
      assert (l1 = fst (proj1_sig l1ht)) as El1. { by rewrite -Heq_l1ht. } 
      assert ([] = snd (proj1_sig l1ht)) as Enil. { by rewrite -Heq_l1ht. } 
      apply conj; try apply conj.
      - rewrite El1. apply sorted_fst_sppair.
      - rewrite El1 Enil. apply perm_sppair_app.
      - move:(length_l2_n(sp:=l1ht)). rewrite -Enil /= => L0.
        by rewrite -L0.
    Qed.

    Program Fixpoint sort_kernel {n} (l1l2:splpair n) {measure n} : sppair := 
      match l1l2 with (l1, l2) => 
        match l2 with
        | [] => slidefb_coat l1l2
        | h :: t => sort_kernel (slidefb_coat l1l2)
        end
      end.
    Obligation 2.
      assert (h :: t = snd (proj1_sig l1l2)) as Eht. { by rewrite -Heq_l1l2. } 
      move:(length_l2_n(sp:=l1l2)). rewrite -Eht /= => L1.
      by rewrite -L1 subn1 /=.
    Qed.
    Obligation 1.
      destruct l1l2. destruct x. destruct l0.
      - rewrite /=. destruct y. destruct a. apply conj.
        apply s. apply p.
      - rewrite /= in Heq_l1l2. inversion Heq_l1l2.
    Qed.
  End Kernel.

  Section Wrap.
    Context (l:list nat).
    Definition n := length l.
    Definition SPL_nill := @SPL nil l.
    Lemma l_splpair : SPL_nill n nil l.
    Proof. apply conj. apply sorted_nil. apply conj. apply Permutation_refl. done. Qed.

    Definition nill : splpair n := (exist (fun ll => match ll with (l1, l2) =>
      SPL_nill n l1 l2 end) (nil, l) l_splpair).
    Definition sort := Eval compute in
      match proj1_sig (sort_kernel nill) with
      (l1, l2) => l1 ++ l2 end.
  End Wrap.

  Goal sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
  Proof. by compute. Qed.
End Sort.
