Require Import List.
Require Import Bool.
Require Import Arith.

Require Extraction.
Require Import ExtrOcamlNatInt.

Definition filter_lte (a: nat) list := filter (fun n=> n <=? a) list.
Definition filter_gt (a: nat) list := filter (fun n=> negb(n <=? a)) list.

Fixpoint quicksort (l: list nat) :=
    match l with
      nil => nil
    | h :: t => let sorted_t := quicksort t in
                    filter_lte h sorted_t
                    ++ h :: filter_gt h sorted_t
    end.

Compute quicksort (nil).
Compute quicksort (1::2::3::6::1::2::1::0::nil).

Fixpoint length (l: list nat) : nat :=
    match l with
      nil => 0
    | a :: tl => 1 + (length (tl))
    end.

Theorem lengthIsCommutative: forall l m : list nat, length(l ++ m) = length(m ++ l).
Proof.
    induction l.
    intros.
    simpl.
    rewrite app_nil_r.
    reflexivity.
    intros.
    simpl.
    rewrite IHl.
    induction m.
    simpl.
    reflexivity.
    simpl.
    rewrite IHm.
    reflexivity.
Qed.

Theorem lengthIsDistributive: forall l j:(list nat), length (l ++ j) = length l + length j.
Proof.
    induction j.
    simpl.
    rewrite app_nil_r.
    firstorder.
    rewrite lengthIsCommutative.
    simpl.
    rewrite Nat.add_succ_r with (n:=length l) (m:=length j).
    rewrite lengthIsCommutative.
    rewrite IHj.
    firstorder.
Qed.

Theorem twoFilterLengthEq: forall n l, length(filter_lte n l) + length(filter_gt n l) = length(l).
Proof.
    intros.
    induction l.
    simpl.
    reflexivity.
    unfold filter_lte.
    assert ((fun n0 : nat => n0 <=? n) a = true \/ (fun n0 : nat => negb(n0 <=? n)) a = true).
    case (a <=? n).
    left; reflexivity.
    right; simpl; reflexivity.
    destruct H.
    simpl.
    rewrite H.
    simpl.
    assert (filter_lte n l = filter (fun n0 : nat => n0 <=? n) l).
    unfold filter_lte.
    firstorder.
    rewrite <- H0.
    rewrite IHl.
    firstorder.
    assert (filter_lte n (a::l) = filter (fun n0 : nat => n0 <=? n) (a::l)).
    unfold filter_lte.
    firstorder.
    rewrite <- H0.
    simpl.
    rewrite H.
    assert((a <=? n) = false).
    rewrite <- negb_involutive with (b:=(a <=? n)).
    rewrite H.
    firstorder.
    rewrite H1.
    simpl.
    rewrite Nat.add_succ_r with (n:=length(filter_lte n l)) (m:=(length (filter_gt n l))).
    rewrite IHl.
    firstorder.
Qed.

Theorem sortLengthUnchanged :
    forall l:(list nat),
    length l = length (quicksort l).
Proof.
    induction l.
    simpl.
    reflexivity.
    simpl.
    rewrite IHl.
    rewrite lengthIsDistributive.
    simpl.
    rewrite Nat.add_succ_r with
        (n:=length(filter_lte a (quicksort l)))
        (m:=(length (filter_gt a (quicksort l)))).
    rewrite twoFilterLengthEq.
    reflexivity.
Qed.

(* https://gist.github.com/adampalay/44b9ac3515469d92cb2f295e6179b8b9 *)

Extraction "quicksort.ml" quicksort.