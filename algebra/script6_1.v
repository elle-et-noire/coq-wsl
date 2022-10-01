From mathcomp
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ZtoRing.

Lemma Zeq_boolP : Equality.axiom Zeq_bool.
Proof.
  move=> x y.
  by apply: (iffP idP); rewrite Zeq_is_eq_bool.
Qed.

Definition Z_eqMixin := EqMixin Zeq_boolP.
Canonical Z_eqType := Eval hnf in EqType _ Z_eqMixin.

Definition Z_pickle (z : Z) : nat :=
  if (0 <=? z)%Z then (Z.abs_nat z).*2
    else (Z.abs_nat (- z)).*2.+1.
    
Definition Z_unpickle (n : nat) : option Z :=
  if odd n then Some (- (Z.of_nat n.-1./2))%Z
    else Some (Z.of_nat n./2).

Lemma Z_pickleK : pcancel Z_pickle Z_unpickle.
Proof.
  move=> z; rewrite/Z_pickle.
  case: ifP => z0.
  rewrite/Z_unpickle.
  rewrite odd_double.
  rewrite (half_bit_double _ false).
  rewrite Zabs2Nat.id_abs.
  rewrite Z.abs_eq.
  rewrite ?Z.opp_nonneg_nonpos.
  rewrite ?Z.opp_involutive.
  rewrite //.
  by apply: Zle_bool_imp_le.

  rewrite/Z_unpickle.
  rewrite /=.
  rewrite odd_double.
  rewrite (half_bit_double _ false).
  rewrite Zabs2Nat.id_abs.
  rewrite Z.abs_eq.
  rewrite ?Z.opp_nonneg_nonpos.
  rewrite ?Z.opp_involutive.
  rewrite //.
  move/Z.leb_nle: z0.
  move/Znot_le_gt.
  move/Z.gt_lt.
  move/Z.lt_le_incl.
  by move/Z.opp_nonneg_nonpos.
Qed.

Lemma Z_pickleK' : pcancel Z_pickle Z_unpickle.
Proof.
  move=> z; rewrite/Z_pickle.
  case: ifP => z0;
  rewrite /Z_unpickle /= odd_double (half_bit_double _ false)
    Zabs2Nat.id_abs Z.abs_eq ?Z.opp_nonneg_nonpos
    ?Z.opp_involutive //.
  - by apply: Zle_bool_imp_le.
  - move/Z.leb_nle: z0.
    by move /Znot_le_gt /Z.gt_lt /Z.lt_le_incl.
Qed.

Definition Z_countMixin := Countable.Mixin Z_pickleK.
Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.

Definition Z_zmodMixin :=
  ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
Canonical Z_zmodType := Eval hnf in ZmodType _ Z_zmodMixin.

End ZtoRing.

Open Scope ring_scope.
Goal forall x: Z, x *+ 2 = (2 * x)%Z.
Proof.
  case=> // x; rewrite GRing.mulr2n Z.mul_comm.
  - by rewrite -(Zred_factor1 (Z.pos x)).
  - by rewrite -(Zred_factor1 (Z.neg x)).
Qed.