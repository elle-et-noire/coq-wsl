From mathcomp
  Require Import ssreflect ssrbool ssrfun ssrnat fintype bigop finset fingroup.

Section Lagrange.
Open Scope group_scope.

Variable gT : finGroupType.
Variable G : {group gT}.

Variable H : {group gT}.
Hypothesis HG : H \subset G.

Definition R := [rel x y | x * y^-1 \in H].

Lemma equiv_rel_R : equivalence_rel R.
Proof.
  rewrite /equivalence_rel => x y z /=.
  apply: pair.
  - by rewrite mulgV group1.
  - move=> xRinvy. apply/idP/idP.
  -- move/(groupM (groupVr xRinvy)). by rewrite invMg invgK mulgA -(mulgA y) mulVg mulg1.
  -- move/(groupM xRinvy). by rewrite mulgA -(mulgA x) mulVg mulg1.
Qed.

Lemma myCard_rcoset (A : {set gT})
  : A \in rcosets H G -> #|A| = #|H|.
Proof.
  case /rcosetsP => a ainG ->.
  by apply: card_rcoset.
Qed.

Lemma coset_equiv_class (x: gT) (xinG: x \in G)
  : H :* x = [set y in G | R x y].
Proof.
  apply /setP => /= y; rewrite inE.
  apply/idP/idP.
  - case /rcosetP => z zinH -> {y}. apply /andP; apply conj.
  -- rewrite groupM //. move /subsetP :HG=> HG'. by move: (HG' _ zinH).
  - by rewrite invMg mulgA mulgV mul1g groupV.
  - case /andP => yinG xinvyinH.
  apply /rcosetP; apply: (ex_intro2 _ _ (y * x^-1)).
  - by rewrite -groupV invMg invgK.
  - by rewrite -(mulgA y) mulVg mulg1.
Qed.

Lemma rcosets_equiv_part : rcosets H G = equivalence_partition R G.
Proof.
  apply /setP => /= X; rewrite /rcosets /equivalence_partition.
  apply/idP/idP.
  - case /rcosetsP => x0 x0inG X_Hx. apply /imsetP. apply: (ex_intro2 _ _ x0).
  -- by [].
  -- by rewrite X_Hx coset_equiv_class.
  -- case /imsetP => x1 xinG Hypo. apply /imsetP. apply: (ex_intro2 _ _ x1).
  --- by [].
  --- by rewrite rcosetE Hypo coset_equiv_class.
Qed.

Lemma partition_rcosets : partition (rcosets H G) G.
Proof.
  rewrite rcosets_equiv_part.
  apply /equivalence_partitionP => x y z xinG yinG zinG.
  by apply: equiv_rel_R.
Qed.

Theorem myLagrange : #|G| = (#|H| * #|G : H|)%nat.
Proof.
  rewrite (card_partition partition_rcosets).
  rewrite ((eq_bigr (fun _ => #|H|)) myCard_rcoset).
  by rewrite sum_nat_const mulnC.
Qed.

Check big_const.
Check iter_addn_0.
   