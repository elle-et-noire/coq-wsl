Generalizable All Variables.
Require Export Coq.Program.Basics Coq.Program.Tactics Coq.Setoids.Setoid Coq.Classes.Morphisms.

(* Obligation Tactic := (try split); program_simpl; try now auto. *)

Module Setoid.
  Structure Setoid : Type := {
    setoid_carrier :> Type;
    setoid_equal: setoid_carrier -> setoid_carrier -> Prop;
    setoid_prf :> Equivalence setoid_equal
  }.
  #[global]
  Existing Instance setoid_prf.

  Notation "[ 'Setoid' 'by' P 'on' A ]" := (@Build_Setoid A P _).
  Notation "[ 'Setoid' 'by' P ]" := [Setoid by P on _].

  Notation "(== 'in' A )" := (setoid_equal A).
  Notation "x == y 'in' A" := (setoid_equal A x y) (at level 70, y at next level, no associativity).
  Notation "(==)" := (== in _).
  Notation "x == y" := (x == y in _) (at level 70, no associativity).

  Program Definition eq_setoid (X:Type) :=
    [Setoid by @eq X].
  Program Definition function (X Y:Type) : Setoid :=
    [Setoid by `(forall x, f x = g x) on X -> Y].
  Next Obligation.
    split; intros x; congruence.
  Defined.
  (* Canonical Structure function. *)

  Inductive empty := .

  Program Definition empty_setoid: Setoid :=
    [Setoid by (fun e e' => match e, e' with end) on empty].
  Next Obligation.
    split; compute; intros x; case x.
  Qed.

  Inductive unit := tt.
  
  Program Definition unit_setoid: Setoid :=
    [Setoid by (fun _ _ => True) on unit].
  Next Obligation.
    split; intros H; tauto.
  Qed.

  Class IsMap {X Y:Setoid} (f: X -> Y) :=
    { map_proper :> Proper ((==) ==> (==)) f }.
  (* Print "==>".
  Locate respectful. *)

  Structure Map (X Y:Setoid): Type := {
    map_fun :> X -> Y;
    map_prf :> IsMap map_fun
  }.
  #[global]
  Existing Instance map_prf.
  
  Notation "[ 'Map' 'by' f ]" := (@Build_Map _ _ f _).
  Notation "[ x 'in' X :-> m ]" := [Map by fun (x:X) => m].
  Notation "[ x :-> m ]" := ([x in _ :-> m]).

  Program Definition Map_compose (X Y Z:Setoid) (f: Map X Y) (g: Map Y Z): Map X Z :=
    [x :-> g (f x)].
  Next Obligation.
    split. intros x y Heq. now rewrite Heq.
  Defined.

  Program Definition Map_id (X:Setoid) : Map X X :=
    [x :-> x].
  Next Obligation.
    split. intros x y Heq. apply Heq.
  Defined.

  Program Definition Map_setoid (X Y: Setoid) : Setoid :=
    [Setoid by `(forall x, f x == g x) on Map X Y].
  Next Obligation.
    split.
    - now intros x x0.
    - intros x y Heq x0. now rewrite Heq.
    - intros x y z Heq1 Heq2 x0. now rewrite Heq1, Heq2.
  Defined.
  Canonical Structure Map_setoid.

  (* Program Definition Map_setoid' (X Y:Setoid) : Setoid :=
    [Setoid by ((==)==>(==))%signature on Map X Y]. *)
End Setoid.
Import Setoid.

Declare Scope group_scope.
Open Scope group_scope.
Module Group.
  Class IsGroup 
        (supp:Setoid)
        (op: supp -> supp -> supp)
        (inv: Map supp supp)
        (id:supp) := 
  {
    grp_op_proper:>
      Proper ((==) ==> (==) ==> (==)) op;
    
    grp_op_assoc:
      forall x y z, op x (op y z) == op (op x y) z;
    
    grp_inv_r:
      forall x, op (inv x) x == id;
    grp_inv_l:
      forall x, op x (inv x) == id;
    
    gpr_id_r:
      forall x, op x id == x
  }.

  Structure Group :=
  {
    grp_supp:> Setoid;
    grp_op: grp_supp -> grp_supp -> grp_supp;
    grp_inv: Map grp_supp grp_supp;
    grp_id:grp_supp;

    grp_prf:> IsGroup grp_supp grp_op grp_inv grp_id
  }.
  #[global]
  Existing Instance grp_prf.

  Notation "[ 'Group' 'by' op , inv , id ]" :=
    (@Build_Group _ op inv id).
  
  Notation "g *_{ G } h" := (@grp_op G g h) (at level 60, right associativity) : group_scope.
  Notation "g * h" := (g *_{_} h) : group_scope.
  Notation "id_{ G }" := (@grp_id G) : group_scope.
  Notation "'id'" := id_{_} : group_scope.
  Notation "!_{ G } g " := (@grp_inv G g) (at level 30, no associativity) : group_scope.
  Notation "! g" := (!_{_} g) (at level 30, no associativity): group_scope.
  Section Test.
    Variables (G:Group) (g h:G).
    Check (!(g*h)).
    Check (!g*h).
  End Test.
End Group.
Import Group.

Close Scope group_scope.

