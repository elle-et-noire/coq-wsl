Class EqDec (A:Type) := {
  eqb : A -> A -> bool;
  eqb_leibniz : forall x y, eqb x y = true -> x = y
}.

#[local]
Instance unit_EqDec : EqDec unit := {
  eqb x y := true;
  eqb_leibniz x y H :=
    match x, y return x = y with
    | tt, tt => eq_refl tt
    end
}.

#[local, refine]
Instance unit_EqDec' : EqDec unit :=
  { eqb x y := true }.
Proof. intros [] []. reflexivity. Defined.

About unit_EqDec'.

Require Import Program.Tactics.

#[local]
Program Instance eq_bool : EqDec bool :=
  { eqb x y := if x then y else negb y }.
Next Obligation.
  destruct x, y; (discriminate || reflexivity).
Defined.

Definition neqb {A} {eqa: EqDec A} (x y:A) := negb (eqb x y).

Generalizable Variables A B C.

Definition neqb_implicit `{eqa: EqDec A} (x y:A) := negb (eqb x y).

#[local]
Program Instance prod_eqb `(EA: EqDec A, EB: EqDec B) : EqDec (A * B) :=
  { eqb x y := match x, y with
    | (la, ra), (lb, rb) => andb (eqb la lb) (eqb ra rb)
    end }.

Section EqDec_defs.
  Context `{EA: EqDec A}.

  #[global, program]
  Instance option_eqb : EqDec (option A) :=
    { eqb x y := match x, y with
      | Some x, Some y => eqb x y
      | None, None => true
      | _, _ => false
      end }.
  Admit Obligations.
End EqDec_defs.

About option_eqb.

Class Ord `(E: EqDec A) :=
  { le: A -> A -> bool }.

(* Class `(E: EqDec A) => Ord A :=
  { le : A -> A -> bool }. *)

Definition le_eqb `{Ord A} (x y:A) :=
  andb (le x y) (le y x).

Definition lt `{eqa: EqDec A, ! Ord eqa} (x y:A) :=
  andb (le x y) (neqb x y).

Require Import Relations.

Class Reflexive (A:Type) (R: relation A) :=
  reflexivity: forall x, R x x.

Class Transitive (A:Type) (R: relation A) :=
  transivity: forall x y z, R x y -> R y z -> R x z.

Class Preorder (A:Type) (R: relation A) :=
  { PreOrder_Reflexive :> Reflexive A R;
    PreOrder_Transitive :> Transitive A R }.

    (* https://coq.inria.fr/refman/addendum/type-classes.html *)