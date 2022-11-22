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
  { map_proper:> Proper ((==) ==> (==)) f }.
  (* Print "==>".
  Locate respectful. *)

  Structure Map (X Y:Setoid): Type := {
    map_fun:> X -> Y;
    map_prf:> IsMap map_fun
  }.
  #[global]
  Existing Instance map_prf.
  
  Notation "[ 'Map' 'by' f ]" := (@Build_Map _ _ f _).
  Notation "[ x 'in' X :-> m ]" := [Map by fun (x:X) => m].
  Notation "[ x :-> m ]" := ([x in _ :-> m]).

  Program Definition Map_compose {X Y Z:Setoid} (f: Map X Y) (g: Map Y Z): Map X Z :=
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

  Definition injective `(f: Map X Y) :=
    forall x y, f x == f y -> x == y.
  Definition surjective `(f: Map X Y) :=
    forall y, exists x, y == f x.
  Definition bijective `(f: Map X Y) :=
    injective f /\ surjective f.
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
      forall {x y z}, op x (op y z) == op (op x y) z;
    
    grp_inv_l:
      forall {x}, op (inv x) x == id;
    grp_inv_r:
      forall {x}, op x (inv x) == id;
    
    grp_id_r:
      forall {x}, op x id == x
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

  Notation "[ 'Group' 'by' op , inv , id 'on' A ]" :=
    (@Build_Group A op inv id _).
  Notation "[ 'Group' 'by' op , inv , id ]" :=
    [Group by op, inv, id on _].
  
  Notation "g *_{ G } h" := (@grp_op G g h) (at level 60, right associativity) : group_scope.
  Notation "g * h" := (g *_{_} h) : group_scope.
  Notation "id_{ G }" := (@grp_id G) : group_scope.
  Notation "'id'" := id_{_} : group_scope.
  Notation "!_{ G } g " := (@grp_inv G g) (at level 30, right associativity) : group_scope.
  Notation "! g" := (!_{_} g) (at level 30, right associativity): group_scope.
End Group.
Import Group.

Section GroupTheory.
  Context {G:Group}.
  Lemma grp_id_l : forall {x:G}, id * x == x.
  Proof.
    intros x. 
    now rewrite <-(grp_inv_r(x:=x)),
      <-grp_op_assoc, (grp_inv_l), grp_id_r.
  Qed.

  Lemma grp_op_inj_l : forall {g x y:G},
    g * x == g * y -> x == y.
  Proof.
    intros g x y Heq.
    assert (!g * g * x == !g * g * y) as H.
    { now rewrite <-2!grp_op_assoc, Heq. }
    now rewrite grp_inv_l, 2!grp_id_l in H.
  Qed.

  Lemma grp_op_inj_r : forall {g x y:G},
    x * g == y * g -> x == y.
  Proof.
    intros g x y Heq.
    assert (x * (g * !g) == y * (g * !g)) as H.
    { now rewrite 2!grp_op_assoc, Heq. }
    now rewrite grp_inv_r, 2!grp_id_r in H.
  Qed.

  Lemma grp_op_feq_l : forall {g x y:G},
    x == y -> g * x == g * y.
  Proof.
    intros g x y Heq. now rewrite Heq.
  Qed.

  Lemma grp_op_feq_r : forall {g x y:G},
    x == y -> x * g == y * g.
  Proof.
    intros g x y Heq. now rewrite Heq.
  Qed.

  Lemma grp_send_l : forall {g x y:G},
    g * x == y -> x == !g * y.
  Proof.
    intros g x y Heq.
    apply (grp_op_inj_l(g:=g)).
    now rewrite grp_op_assoc, grp_inv_r, grp_id_l.
  Qed.

  Lemma grp_send_r : forall {g x y:G},
    x * g == y -> x == y * !g.
  Proof.
    intros g x y Heq.
    apply (grp_op_inj_r(g:=g)).
    now rewrite <-grp_op_assoc, grp_inv_l, grp_id_r.
  Qed.
  
  Lemma grp_invinv : forall {x:G}, !!x == x.
  Proof.
    intros x.
    assert (!!x * !x == x * !x) as H.
    { now rewrite grp_inv_l, grp_inv_r. }
    now apply grp_op_inj_r in H.
  Qed.

  Lemma grp_opinv : forall {x y:G},
    !(x * y) == !y * !x.
  Proof.
    intros x y. 
    rewrite <-(grp_id_r(x:=!y*!x)), <-grp_op_assoc.
    apply grp_send_l, grp_send_l.
    now rewrite grp_op_assoc, grp_inv_r.
  Qed.

  Lemma grp_invid_id : !id_{G} == id.
  Proof.
    rewrite <-(grp_id_r(x:=!id)).
    symmetry; apply grp_send_l, grp_id_l.
  Qed.
End GroupTheory.

Module Hom.
  Class IsHom {G H:Group} (f: Map G H) := {
    hom_proper:
      forall {x y:G}, f (x * y) == (f x) * (f y)
  }.

  Structure Hom (G H:Group) := {
    hom_map:> Map G H;
    
    hom_prf:> IsHom hom_map
  }.
  #[global]
  Existing Instance hom_prf.

  Notation "[ 'Hom' 'by' f ]" := (@Build_Hom _ _ [Map by f] _) : group_scope.
  Notation "[ x 'in' G :-> m ]" := [Hom by fun (x:G) => m] : group_scope.
  Notation "[ x :-> m ]" := ([x in _ :-> m]) : group_scope.

  Class IsIsomorph `(f: Hom G H) := {
    iso_proper: bijective f
  }.

  Structure Isomorph (G H:Group):= {
    iso_map:> Hom G H;

    iso_prf:> IsIsomorph iso_map
  }.
  #[global]
  Existing Instance iso_prf.
  Notation "[ 'Iso' 'by' f ]" := (@Build_Isomorph _ _ [Hom by f] _) : group_scope.
  Notation "[ x 'in' G :=> m ]" := [Iso by fun (x:G) => m] : group_scope.
  Notation "[ x :=> m ]" := ([x in _ :=> m]) : group_scope.
End Hom.
Import Hom.

Section HomTheory.
  Context {G H:Group} {f: Hom G H}.
  Lemma hom_id : f id == id.
  Proof.
    rewrite <-(grp_inv_r(x:=f id)).
    apply grp_send_r. now rewrite <-hom_proper, grp_id_r.
  Qed.

  Lemma hom_inv : forall x, f (!x) == ! f x.
  Proof.
    intros x.
    rewrite <-(grp_id_r(x:=!f x)).
    apply grp_send_l.
    now rewrite <-hom_proper, grp_inv_r, hom_id.
  Qed.
End HomTheory.

Module SubGroup.
  Class IsSubGroup (G:Group) (H: G -> Prop) :=
  {
    sg_conf_proper:
      forall {x y}, x == y -> H x -> H y;

    sg_ferm_op:
      forall {x y}, H x -> H y -> H (x * y);
    
    sg_ferm_inv:
      forall {x}, H x -> H (!x);
    
    sg_ferm_id: H id
  }.

  Structure SubGroup := {
    sg_G: Group;
    sg_H:> sg_G -> Prop;

    sg_prf:> IsSubGroup sg_G sg_H
  }.
  #[global]
  Existing Instance sg_prf.
  
  Notation "[ 'SubGroup' H 'on' G ]" :=
    (@Build_SubGroup G H _).
  Notation "[ 'SubGroup' 'of' x : G | P ]" :=
    [SubGroup (fun x => P) on G].
  Notation "[ 'SubGroup' 'of' x | P ]" :=
    [SubGroup (fun x => P) on _].

  Program Definition sg_as_setoid (H:SubGroup) :=
    [Setoid by (fun x y => proj1_sig x == proj1_sig y) on {x|H x}].
  Next Obligation.
    split.
    - now intros x.
    - intros x y Heq. now symmetry.
    - intros x y z Heq1 Heq2. now rewrite Heq1, Heq2.
  Defined.
  Coercion sg_as_setoid : SubGroup >-> Setoid.

  Program Definition sg_as_group (H:SubGroup) :=
    [Group by (fun x y => x * y),
              [Map by fun x => !x], 
              (id_{sg_G H}) on H].
  Next Obligation.
    apply sg_ferm_op; (apply H1 || apply H0).
  Defined.
  Next Obligation.
    apply sg_ferm_inv, H0.
  Defined.
  Next Obligation.
    split. intros x y. simpl. now intros Heq; rewrite Heq.
  Defined.
  Next Obligation.
    apply sg_ferm_id.
  Defined.
  Next Obligation.
    split.
    - intros x1 x2 Heq_x y1 y2 Heq_y. simpl.
      apply grp_op_proper; (apply Heq_x || apply Heq_y).
    - intros x y z. simpl. apply grp_op_assoc.
    - intros x. simpl. apply grp_inv_l.
    - intros x. simpl. apply grp_inv_r.
    - intros x. simpl. apply grp_id_r.
  Defined.
  Coercion sg_as_group : SubGroup >-> Group.

  Class IsNormalSG (H:SubGroup) := {
    nsg_proper:
      forall {g h}, H h -> H (g * h * !g)
  }.

  Structure NormalSG := {
    nsg_H:> SubGroup;

    nsg_prf:> IsNormalSG nsg_H
  }.
  #[global]
  Existing Instance nsg_prf.

  Notation "[ 'NSG' H 'on' G ]" :=
    (@Build_NormalSG [SubGroup H on G] _).
  Notation "[ 'NSG' 'of' x : G | P ]" :=
    [NSG (fun x => P) on G].
  Notation "[ 'NSG' 'of' x | P ]" :=
    [NSG (fun x => P) on _].
End SubGroup.
Import SubGroup.

Section HomTheory.
  Context {G H:Group} (f: Hom G H).
  Program Definition ImageSG := 
    [SubGroup of y | exists x, y == f x].
  Next Obligation.
    split.
    - intros x y Heq1 [z Heq2].
      exists z. now rewrite <-Heq1.
    - intros x y [z_x Heq1] [z_y Heq2].
      exists (z_x * z_y).
      now rewrite Heq1, Heq2, hom_proper.
    - intros x [y Heq].
      exists (!y).
      now rewrite hom_inv, Heq.
    - exists id. symmetry; apply hom_id.
  Defined.
  
  Program Definition confimg : Hom G ImageSG :=
    [g :-> f g].
  Next Obligation.
    now exists g.
  Defined.
  Next Obligation.
    split. intros x y Heq. simpl. now rewrite Heq.
  Defined.
  Next Obligation.
    split. intros x y. simpl. apply hom_proper.
  Defined.
  (* Canonical confimg. *)

  Lemma confimg_surj : surjective confimg.
  Proof.
    intros [h [g Heq]]. simpl. now exists g.
  Qed.

  Program Definition inc : Hom ImageSG H :=
    [h :-> h].
  Next Obligation.
    split. intros x y. now simpl.
  Defined.
  Next Obligation.
    split. intros x y. now simpl.
  Defined.

  Lemma inc_inj : injective inc.
  Proof.
    intros x y. now simpl.
  Qed.

  Program Definition KernelNSG :=
    [NSG of x | f x == id].
  Next Obligation.
    split.
    - intros x y Heq1 Heq2. now rewrite <-Heq1. 
    - intros x y Heq1 Heq2.
      now rewrite hom_proper, Heq1, Heq2, grp_id_r.
    - intros x Heq.
      now rewrite hom_inv, Heq, grp_invid_id.
    - apply hom_id.
  Defined.
  Next Obligation.
    split. intros g h. simpl. intros Heq.
    now rewrite 2!hom_proper, Heq, grp_id_r,
      <-hom_proper, grp_inv_r, hom_id.
  Defined.
End HomTheory.

Ltac Hrewrite Heq := apply (sg_conf_proper Heq).
Ltac Hrewriteto x := apply (sg_conf_proper(x:=x)).

Module Coset.
  Program Definition Coset (H:SubGroup) :=
    [Setoid by (fun x y => H (x * !y)) on (sg_G H)].
  Next Obligation.
    split.
    - intros x. 
      apply (sg_conf_proper (symmetry grp_inv_r)), sg_ferm_id.
    - intros x y Heq.
      apply (sg_conf_proper grp_invinv), sg_ferm_inv.
      apply (sg_conf_proper (symmetry grp_opinv)).
      now apply (sg_conf_proper(x:=x*!y)); (rewrite grp_invinv || idtac).
    - intros x y z Hxy Hyz. 
      apply (sg_conf_proper(x:=(x*!y)*(y*!z))).
     -- now rewrite grp_op_assoc, <-(grp_op_assoc(x:=x)), 
          grp_inv_l, grp_id_r.
     -- apply sg_ferm_op; (apply Hxy || apply Hyz).
  Defined.

  Program Definition proj {H:SubGroup} : Map (sg_G H) (Coset H) :=
    [Map by fun x => x].
  Next Obligation.
    split. intros x y Heq. simpl. Hrewriteto id_{sg_G H}.
    - now rewrite Heq, grp_inv_r.
    - apply sg_ferm_id.
  Defined.

  Program Definition CosetGroup (H:NormalSG) :=
    [Group by (fun x y => x * y), [Map by fun x => !x], id
    on Coset H].
  Next Obligation.
    split. intros x y. simpl. intros Heq. Hrewriteto (!(!y*x)).
    - now rewrite <-grp_opinv.
    - apply sg_ferm_inv. Hrewriteto (!y * (x * !y) * !!y).
     -- now rewrite grp_invinv, grp_op_assoc,
          <-(grp_op_assoc(y:=!y)), grp_inv_l, grp_id_r.
     -- now apply nsg_proper.
  Defined.
  Next Obligation.
    split.
    - intros x1 y1. simpl. intros Heq1 x2 y2 Heq2.
      Hrewriteto (x1 * (x2 * !y2) * !x1 * (x1 * !y1)).
     -- rewrite grp_opinv, 3!grp_op_assoc.
        apply grp_op_feq_r. 
        now rewrite <-grp_op_assoc, grp_inv_l, grp_id_r.
     -- apply (nsg_proper(g:=x1)) in Heq2. 
        apply (sg_ferm_op Heq2 Heq1).
    - intros x y z. simpl. Hrewriteto id_{sg_G H}.
     -- now rewrite grp_op_assoc, grp_inv_r.
     -- apply sg_ferm_id.
    - intros x. simpl. Hrewriteto id_{sg_G H}.
     -- now rewrite grp_inv_l, grp_id_l, grp_invid_id.
     -- apply sg_ferm_id.
    - intros x. simpl. Hrewriteto id_{sg_G H}.
     -- now rewrite grp_inv_r, grp_id_l, grp_invid_id.
     -- apply sg_ferm_id.
    - intros x. simpl. apply nsg_proper, sg_ferm_id.
  Defined.
  
End Coset.
Import Coset.

Section FundHom.
  Context {G H:Group} (f: Hom G H) (N := KernelNSG f)
    (G_N := CosetGroup N).
  
  Program Definition psi : Isomorph G_N (ImageSG f):=
    [x :=> f x].
  Next Obligation.
    now exists x.
  Defined.
  Next Obligation.
    split. intros x y. simpl. intros Heq.
    rewrite hom_proper, hom_inv in Heq.
    apply grp_send_r in Heq.
    now rewrite grp_invinv, grp_id_l in Heq.
  Defined.
  Next Obligation.
    split. intros x y. simpl. apply hom_proper.
  Defined.
  Next Obligation.
    split. apply conj.
    - intros x y. simpl. intros Heq.
      rewrite hom_proper, hom_inv.
      symmetry; apply grp_send_r.
      now rewrite grp_id_l.
    - intros [y [x Heq]]. simpl. now exists x.
  Defined.

  Lemma psicomp_proper :
    f == Map_compose proj (Map_compose psi (inc _)) in (Map_setoid G H).
  Proof.
    intros g. now simpl.
  Qed.

  Lemma psi_identified : forall (psi0: Hom G_N H), 
    f == Map_compose proj psi0 in (Map_setoid G H) ->
    psi0 == Map_compose psi (inc _) in (Map_setoid G_N H).
  Proof.
    simpl. now intros psi0 Hiso g.
  Qed.
End FundHom.

Close Scope group_scope.

