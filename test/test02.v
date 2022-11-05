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

Print Empty_set.