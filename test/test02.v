Theorem comadd : forall n m : nat, n + m = m + n.
Print "+".
induction n.
induction m.
reflexivity.
simpl. rewrite <-IHm. reflexivity.
simpl. induction m. 
rewrite IHn. simpl. reflexivity.
rewrite IHn. simpl. rewrite <-IHm. rewrite IHn. reflexivity.
Qed.

Theorem asocadd : forall l m n : nat, (l + m) + n = l + (m + n).
Proof.
induction l.
reflexivity.
simpl. intros m n. apply f_equal. apply IHl.
Qed. 

Print "*".
Print "-".

Theorem commul : forall n m : nat, n * m = m * n.
Proof.
induction n.
simpl. induction m.
reflexivity.
simpl. apply IHm.
induction m.
simpl. apply IHn.
simpl. apply f_equal. rewrite <-IHm. rewrite IHn.
simpl. rewrite <-2asocadd. rewrite (comadd m n). rewrite IHn.
reflexivity.
Qed.

Print comadd.
Print eq_refl.
Print f_equal.
Print nat_ind.
Print "=".
Check eq 1 1.
Check eq_refl 1.

Goal 1 = 1.
apply eq_refl.
Qed.

Print Empty_set.

Print False_ind.
Lemma F : forall (f:False) (P: False -> Prop), P f.
Proof. tauto. Qed.

Definition optionPeel {A:Type}(x:option A)(H:exists t, x = Some t): A.
  refine (match x as v return (x = v) -> A with
            | None => fun H1 => _
            | Some t => fun _ => t
          end eq_refl).
  exfalso. destruct H as [t H2]. rewrite H2 in H1; discriminate H1.
Defined.