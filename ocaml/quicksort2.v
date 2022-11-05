(* Largely inspired by https://github.com/coq/coq/wiki/QuickSort *)
Require Import Arith.Wf_nat Bool List Nat Lia.
Require Import Sorting.Permutation Sorting.Sorted.

Definition flip_ltb (x : nat) : nat -> bool :=
  fun (y : nat) => y <? x.

Definition flip_geb (x : nat) : nat -> bool :=
  fun (y : nat) => x <=? y.

Inductive QSAcc : list nat -> Prop :=
| QSAccNil  : QSAcc nil
| QSAccCons : forall x xs,
              QSAcc (filter (flip_ltb x) xs) ->
              QSAcc (filter (flip_geb x) xs) ->
              QSAcc (x :: xs).

Lemma QSAcc_inv_1 :
  forall {x xs l},
  QSAcc l -> l = (x :: xs) ->
  QSAcc (filter (flip_ltb x) xs).
Proof. intros. subst. inversion H. auto. Defined.

Lemma QSAcc_inv_2 :
  forall {x xs l},
  QSAcc l -> l = (x :: xs) ->
  QSAcc (filter (flip_geb x) xs).
Proof. intros. subst. inversion H. auto. Defined.

Fixpoint quickSort' (l : list nat) (acc : QSAcc l) {struct acc} : list nat :=
  match l as l0 return (l = l0 -> list nat) with
  | nil =>
      fun (_ : l = nil) => nil
  | x :: xs =>
      fun (H : l = (x :: xs)) =>
      quickSort' (filter (flip_ltb x) xs) (QSAcc_inv_1 acc H) ++
      x :: quickSort' (filter (flip_geb x) xs) (QSAcc_inv_2 acc H)
  end (eq_refl l).

Lemma induction_ltof1_Prop
     : forall (A : Set) (f : A -> nat) (P : A -> Prop),
       (forall x : A, (forall y : A, ltof A f y x -> P y) -> P x) ->
       forall a : A, P a.
Proof.
  intros A f P F.
  assert (H : forall (n : nat) (a : A), f a < n -> P a).
  { induction n; intros.
    - omega.
    - apply F. unfold ltof. intros. apply IHn.
      apply Nat.lt_le_trans with (m := f a); omega. }
  intros. apply H with (n := S (f a)). omega.
Defined.

Lemma filter_length :
  forall {a} (f : a -> bool) (l : list a),
  length (filter f l) <= length l.
Proof.
  induction l; simpl; auto.
  destruct (f a0); simpl; auto. omega.
Defined.

Theorem qsAcc : forall l, QSAcc l.
Proof.
  intros. apply (induction_ltof1_Prop _ (@length nat)).
  intros. destruct x as [|x xs]; constructor; apply H; unfold ltof; simpl.
  - pose proof (filter_length (flip_ltb x) xs). omega.
  - pose proof (filter_length (flip_geb x) xs). omega.
Defined.
Scheme QSAcc_ind_dep := Induction for QSAcc Sort Prop.

Definition quickSort (l : list nat) : list nat :=
  quickSort' l (qsAcc l).

Lemma unit_test : quickSort (2 :: 3 :: 1 :: nil) = 1 :: 2 :: 3 :: nil.
Proof. auto. Qed.

Lemma quickSort'_PI' :
  forall {l1} (acc1 : QSAcc l1) {l2} (acc2 : QSAcc l2),
  l1 = l2 ->
  quickSort' l1 acc1 = quickSort' l2 acc2.
Proof.
  apply (QSAcc_ind_dep
          (fun (l' : list nat) (acc' : QSAcc l') =>
           forall (l2 : list nat) (acc2 : QSAcc l2),
           l' = l2 -> quickSort' l' acc' = quickSort' l2 acc2)).
  - apply (QSAcc_ind_dep
            (fun (l' : list nat) (acc' : QSAcc l') =>
             nil = l' ->
             quickSort' nil QSAccNil = quickSort' l' acc')); try discriminate. auto.
  - intros until 2.
    apply (QSAcc_ind_dep
            (fun (l' : list nat) (acc' : QSAcc l') =>
             x :: xs = l' ->
             quickSort' (x :: xs) (QSAccCons x xs q q0) = quickSort' l' acc')); try discriminate.
    intros. injection H3 as H4 H5. subst. simpl.
    pose proof (H  (filter (flip_ltb x0) xs0) (QSAcc_inv_1 (QSAccCons x0 xs0 q q0) eq_refl) eq_refl).
    pose proof (H0 (filter (flip_geb x0) xs0) (QSAcc_inv_2 (QSAccCons x0 xs0 q q0) eq_refl) eq_refl).
    rewrite <- H3. rewrite <- H4.
    pose proof (H  (filter (flip_ltb x0) xs0) (QSAcc_inv_1 (QSAccCons x0 xs0 q1 q2) eq_refl) eq_refl).
    pose proof (H0 (filter (flip_geb x0) xs0) (QSAcc_inv_2 (QSAccCons x0 xs0 q1 q2) eq_refl) eq_refl).
    rewrite <- H5. rewrite <- H6. auto.
Qed.

Lemma quickSort'_PI :
  forall {l} (acc1 acc2 : QSAcc l),
  quickSort' l acc1 = quickSort' l acc2.
Proof. intros. rewrite (quickSort'_PI' acc1 acc2); auto. Qed.

Theorem quickSort'_nil :
  forall (acc : QSAcc nil),
  quickSort' nil acc = nil.
Proof. intros. rewrite (quickSort'_PI acc QSAccNil). auto. Qed.

Theorem quickSort_nil :
  quickSort nil = nil.
Proof. auto. Qed.

Theorem quickSort'_cons :
  forall {x xs} (acc   : QSAcc (x :: xs))
                (accLT : QSAcc (filter (flip_ltb x) xs))
                (accGE : QSAcc (filter (flip_geb x) xs)),
  quickSort' (x :: xs) acc =
    quickSort' (filter (flip_ltb x) xs) accLT ++
    x :: quickSort' (filter (flip_geb x) xs) accGE.
Proof. intros. rewrite (quickSort'_PI acc (QSAccCons x xs accLT accGE)). auto. Qed.

Theorem quickSort'_cons_exists :
  forall {x xs} (acc : QSAcc (x :: xs)),
  exists (accLT : QSAcc (filter (flip_ltb x) xs))
         (accGE : QSAcc (filter (flip_geb x) xs)),
  quickSort' (x :: xs) acc =
    quickSort' (filter (flip_ltb x) xs) accLT ++
    x :: quickSort' (filter (flip_geb x) xs) accGE.
Proof.
  intros.
  pose proof (qsAcc (filter (flip_ltb x) xs)) as accLT.
  pose proof (qsAcc (filter (flip_geb x) xs)) as accGE.
  exists accLT. exists accGE.
  rewrite (quickSort'_PI acc (QSAccCons x xs accLT accGE)). auto.
Qed.

Theorem quickSort_cons_QSAccCons :
  forall {x xs} (accLT : QSAcc (filter (flip_ltb x) xs))
                (accGE : QSAcc (filter (flip_geb x) xs)),
  quickSort' (x :: xs) (QSAccCons x xs accLT accGE) =
    quickSort' (filter (flip_ltb x) xs) accLT ++
    x :: quickSort' (filter (flip_geb x) xs) accGE.
Proof. intros. rewrite (quickSort'_cons _ accLT accGE). auto. Qed.

Theorem quickSort_cons :
  forall {x xs},
  quickSort (x :: xs) =
    quickSort (filter (flip_ltb x) xs) ++
    x :: quickSort (filter (flip_geb x) xs).
Proof. intros. unfold quickSort. apply quickSort'_cons. Qed.

Hint Resolve Nat.ltb_spec0 Nat.leb_spec0 Nat.eqb_spec : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Lemma HdRel_app :
  forall (a : nat) (c : nat) (bs : list nat) (ds : list nat),
  a <= c -> HdRel le a bs ->
  HdRel le a (bs ++ c :: ds).
Proof.
  induction bs; simpl; intros.
  - constructor. auto.
  - inversion H0. constructor. auto.
Qed.

Lemma HdRel_extend :
  forall (a b : nat) (l : list nat),
  a <= b -> HdRel le b l ->
  HdRel le a l.
Proof.
  intros. destruct l.
  - auto.
  - constructor. inversion H0. subst. omega.
Qed.

Lemma HdRel_filter :
  forall (a : nat) (f : nat -> bool) (l : list nat),
  Sorted le l -> HdRel le a l ->
  HdRel le a (filter f l).
Proof.
  intros. induction H; simpl.
  - auto.
  - inversion H0. subst. destruct (f a0).
    + constructor. auto.
    + apply IHSorted. apply HdRel_extend with (b := a0); auto.
Qed.

Lemma Sorted_partition :
  forall (x : nat) (l1 l2 : list nat),
  Sorted le l1 -> Sorted le l2 ->
  (forall y, In y l1 -> y <  x) ->
  (forall y, In y l2 -> x <= y) ->
  Sorted le (l1 ++ x :: l2).
Proof.
  intros until 1. revert l2. induction H; simpl.
  - intros. constructor; auto. destruct l2.
    + auto.
    + constructor. inversion H. subst. apply H1. left. auto.
  - intros. constructor; auto.
    assert (AX : a < x). { apply H2. left. auto. }
    apply HdRel_app.
    + omega.
    + auto.
Qed.

Lemma Sorted_filter :
  forall (f : nat -> bool) (l : list nat),
  Sorted le l -> Sorted le (filter f l).
Proof.
  intros. induction H; simpl.
  - auto.
  - destruct (f a); auto. constructor; auto. apply HdRel_filter; auto.
Qed.

Lemma In_filter_ltb :
  forall (x y : nat) (l : list nat),
  In y (filter (flip_ltb x) l) ->
  y < x.
Proof.
  intros. induction l.
  - contradiction.
  - simpl in H. unfold flip_ltb in H. bdestruct (a <? x); auto.
    simpl in H. destruct H; auto. subst. auto.
Qed.

Lemma In_filter_geb :
  forall (x y : nat) (l : list nat),
  In y (filter (flip_geb x) l) ->
  x <= y.
Proof.
  intros. induction l.
  - contradiction.
  - simpl in H. unfold flip_geb in H. bdestruct (x <=? a); auto.
    simpl in H. destruct H; auto. subst. auto.
Qed.

Lemma In_quickSort' :
  forall x l acc,
  In x (quickSort' l acc) -> In x l.
Proof.
  intro x.
  apply (QSAcc_ind_dep
          (fun (l' : list nat) (acc' : QSAcc l') =>
           In x (quickSort' l' acc') -> In x l')).
  - auto.
  - intros. rewrite (quickSort_cons_QSAccCons q q0) in H1.
    simpl. apply in_app_or in H1. destruct H1.
    + specialize (H H1).
      pose proof (filter_In (flip_ltb x0) x xs).
      destruct H2. specialize (H2 H). destruct H2. right. auto.
    + destruct H1.
      * left. auto.
      * specialize (H0 H1).
        pose proof (filter_In (flip_geb x0) x xs).
        destruct H2. specialize (H2 H0). destruct H2. right. auto.
Qed.

Lemma Permutation_filter_ltb_geb :
  forall (x : nat) (l : list nat),
  Permutation l (filter (flip_ltb x) l ++ filter (flip_geb x) l).
Proof.
  induction l; simpl.
  - constructor.
  - unfold flip_ltb, flip_geb.
    bdestruct (a <? x); bdestruct (x <=? a); try omega.
    + constructor; auto.
    + apply Permutation_cons_app. auto.
Qed.

Theorem quickSort'_Sorted :
  forall l (acc : QSAcc l),
  Sorted le (quickSort' l acc).
Proof.
  apply (QSAcc_ind_dep
          (fun (l' : list nat) (acc' : QSAcc l') =>
           Sorted le (quickSort' l' acc'))).
  - constructor.
  - intros. rewrite (quickSort_cons_QSAccCons q q0).
    apply Sorted_partition; auto; intros.
    + apply In_quickSort' in H1. apply In_filter_ltb in H1. auto.
    + apply In_quickSort' in H1. apply In_filter_geb in H1. auto.
Qed.

Theorem quickSort'_Permutation' :
  forall l (acc : QSAcc l),
  Permutation l (quickSort' l acc).
Proof.
  apply (QSAcc_ind_dep
          (fun (l' : list nat) (acc' : QSAcc l') =>
           Permutation l' (quickSort' l' acc'))).
  - constructor.
  - intros. rewrite (quickSort_cons_QSAccCons q q0).
    apply Permutation_cons_app.
    apply Permutation_trans with
      (l' := filter (flip_ltb x) xs ++ filter (flip_geb x) xs).
    + apply Permutation_filter_ltb_geb.
    + apply Permutation_app; auto.
Qed.

Theorem quickSort_correct :
  forall l,
  Sorted le (quickSort l) /\ Permutation l (quickSort l).
Proof. unfold quickSort; split.
- apply quickSort'_Sorted.
- apply quickSort'_Permutation'.
Qed.