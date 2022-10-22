From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Monoid.
  Section ClassDef.
    Record class_of (G:Type) :=
      Class {
          op : G -> G -> G;
          id : G;
          _: associative op;
          _: left_id id op;
          _: right_id id op
        }.

    Structure type := Pack {sort; _: class_of sort}.
    Variable (cT : type).
    Definition class :=
      let: Pack _ c := cT return class_of (sort cT) in c.
  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.

    Notation monoidType := type.
    Definition opg G := op (class G).
    Definition idg G := id (class G).
  End Exports.
End Monoid.
Import Monoid.Exports.

Section MonoidTheory.
  Variable (G:monoidType).

  Lemma opgA : associative (@opg G).
  Proof. by case : G =>[s []]. Qed.

  Lemma op0g : left_id (idg G) (@opg _).
  Proof. by case : G =>[s []]. Qed.

  Lemma opg0 : right_id (idg G) (@opg _).
  Proof. by case : G =>[s []]. Qed.

  Lemma idg_uniquel (e:G) : left_id e (@opg _) -> e = idg G.
  Proof.
    move =>/(_ (idg _)). by rewrite opg0.
  Qed.
End MonoidTheory.

Definition nat_monoid_class_of : Monoid.class_of nat :=
  Monoid.Class addnA add0n addn0.
Canonical nat_monoid : monoidType :=
  @Monoid.Pack nat nat_monoid_class_of.

Lemma my_addn0 : forall n : nat, n + 0 = n.
Proof. exact : opg0. Qed.


Module Comoid.
  Record mixin_of (G:monoidType) :=
    Mixin {
        _: commutative (@opg G)
      }.

  Section ClassDef.
    Record class_of (G:Type) :=
      Class {
          base : Monoid.class_of G;
          mixin : mixin_of (Monoid.Pack base)
        }.
    Structure type := Pack {sort; _: class_of sort}.
    Variable (cT : type).
    Definition class :=
      let: Pack _ c := cT return class_of (sort cT) in c.

    Definition monoidType := Monoid.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Monoid.class_of.
    Coercion mixin : class_of >-> mixin_of.

    Coercion sort : type >-> Sortclass.

    Coercion monoidType : type >-> Monoid.type.
    Canonical monoidType.

    Notation comoidType := type.
  End Exports.
End Comoid.
Import Comoid.Exports.

Section ComoidTheory.
  Variable (G:comoidType).

  Lemma opgC : commutative (@opg G).
  Proof. by case : G =>[s [b []]]. Qed.
End ComoidTheory.


Module Group.
  Record mixin_of (G:monoidType) :=
    Mixin {
        inv : G -> G;
        _: left_inverse (idg G) inv (@opg _)
      }.

  Section ClassDef.
    Record class_of (G:Type) :=
      Class {
          base : Monoid.class_of G;
          mixin : mixin_of (Monoid.Pack base)
        }.
    Structure type := Pack {sort; _: class_of sort}.
    Variable (cT : type).
    Definition class :=
      let: Pack _ c := cT return class_of (sort cT) in c.

    Definition monoidType := Monoid.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Monoid.class_of.
    Coercion mixin : class_of >-> mixin_of.

    Coercion sort : type >-> Sortclass.

    Coercion monoidType : type >-> Monoid.type.
    Canonical monoidType.

    Notation groupType := type.
    Definition invg G := inv (class G).
  End Exports.
End Group.
Import Group.Exports.


Module ComGroup.
  Section ClassDef.
    Record class_of (G:Type) :=
      Class {
          base : Group.class_of G;
          mixin : Comoid.mixin_of (Monoid.Pack base)
        }.
    Definition base2 G (class:class_of G) : Comoid.class_of G :=
      Comoid.Class (mixin class).

    Structure type := Pack {sort; _: class_of sort}.
    Variable (cT : type).
    Definition class :=
      let: Pack _ c := cT return class_of (sort cT) in c.

    Definition monoidType := Monoid.Pack (base class).
    Definition groupType := Group.Pack (base class).
    Definition comoidType := Comoid.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Group.class_of.
    Coercion base2 : class_of >-> Comoid.class_of.

    Coercion sort : type >-> Sortclass.

    Coercion monoidType : type >-> Monoid.type.
    Canonical monoidType.
    Coercion groupType : type >-> Group.type.
    Canonical groupType.    
    Coercion comoidType : type >-> Comoid.type.
    Canonical comoidType.

    Notation comGroupType := type.
  End Exports.
End ComGroup.
Import ComGroup.Exports.

Locate monoidType.
Check Comoid.monoidType.