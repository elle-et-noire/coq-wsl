Generalizable All Variables.
Require Export Coq.Program.Basics Coq.Program.Tactics
  Coq.Setoids.Setoid Coq.Classes.Morphisms.

Declare Scope setoid_scope.
Open Scope setoid_scope.

Structure Setoid : Type := {
  setoid_carrier:> Type;
  setoid_equal: relation setoid_carrier;
  setoid_prf:> Equivalence setoid_equal
}.
#[global]
Existing Instance setoid_prf.

Notation "[ 'setoid' 'by' P 'on' A ]" := (@Build_Setoid A P _).
Notation "[ 'setoid' 'by' P ]" := [setoid by P on _].

Notation "(== 'in' A )" := (setoid_equal A).
Notation "x == y 'in' A" := (setoid_equal A x y)
  (at level 70, y at next level, no associativity).
Notation "(==)" := (== in _).
Notation "x == y" := (x == y in _) (at level 70, no associativity).


Program Definition eq_setoid (X:Type) :=
  [setoid by @eq X].

Program Definition function (X Y:Type) : Setoid :=
  [setoid by `(forall x, f x = g x) on X -> Y].
Next Obligation.
  split; intros x; congruence.
Defined.
Canonical Structure function.

Program Definition prop_setoid := [setoid by iff].
Canonical Structure prop_setoid.

Inductive empty := .

Program Definition empty_setoid: Setoid :=
  [setoid by (fun e e' => match e, e' with end) on empty].
Next Obligation.
  split; compute; intros x; case x.
Qed.

Inductive unit := tt.

Program Definition unit_setoid: Setoid :=
  [setoid by (fun _ _ => True) on unit].
Next Obligation.
  split; intros H; tauto.
Qed.


Class IsSubSetoid (X:Setoid) (conf: X -> Prop) := 
{ subconf_proper:> Proper ((==) ==> (==)) conf }.

Structure SubSetoid (X:Setoid) := {
  sub_conf:> X -> Prop;
  sub_prf:> IsSubSetoid X sub_conf
}.
#[global]
Existing Instance sub_prf.

Notation "[ 'subsetoid' 'by' conf 'on' A ]" :=
  (@Build_SubSetoid A conf _).
Notation "[ 'subsetoid' 'by' conf ]" :=
  [subsetoid by conf on _].
Notation "[ 'subsetoid' 'of' x 'in' A | P ]" :=
  [subsetoid by (fun x => P) on A].
Notation "[ 'subsetoid' 'of' x | P ]" :=
  [subsetoid of x in _ | P].

Program Definition subsetoid_as_setoid `(B: SubSetoid A) :=
  [setoid by (== in A) on {x|B x}].
Next Obligation.
  split.
  - now intros x.
  - intros x y Heq. now symmetry.
  - intros x y z Heq1 Heq2. now rewrite Heq1.
Defined.
Coercion subsetoid_as_setoid : SubSetoid >-> Setoid.

Program Definition subsetoid_trivial (A:Setoid) :=
  [subsetoid of x | True].
Next Obligation. split. now intros x y Heq. Defined.
(* Coercion subsetoid_trivial : Setoid >-> SubSetoid. *)

Class IsMap {X Y:Setoid} (f: X -> Y) :=
{ map_proper:> Proper ((==) ==> (==)) f }.

Structure Map (X Y:Setoid): Type := {
  map_fun:> X -> Y;
  map_prf:> IsMap map_fun
}.
#[global]
Existing Instance map_prf.

Notation "[ 'map' 'by' f ]" := (@Build_Map _ _ f _) : setoid_scope.
Notation " 'map' x 'in' X => m " := [map by fun (x:X) => m]
  (at level 70, right associativity) : setoid_scope.
Notation " 'map' x => m " := (map x in _ => m)
  (at level 70, right associativity) : setoid_scope.

Program Definition Map_compose {X Y Z} (f: Map X Y) (g: Map Y Z)
  : Map X Z := map x => g (f x).
Next Obligation.
  split. intros x y Heq. now rewrite Heq.
Defined.

Program Definition Map_id (X:Setoid) : Map X X := map x => x.
Next Obligation.
  split. intros x y Heq. apply Heq.
Defined.

Program Definition Map_setoid (X Y: Setoid) : Setoid :=
  [setoid by ((==) ==> (==))%signature on Map X Y].
Next Obligation.
  split.
  - intros f x y Heq. now rewrite Heq. 
  - intros f g Heq1 x y Heq2. now rewrite (Heq1 y x (symmetry Heq2)).
  - intros f g h Heq1 Heq2 x y Heq3. 
    now rewrite (Heq1 x y Heq3), <-(Heq2 x y Heq3), Heq3.
Defined.
Canonical Structure Map_setoid.

Notation "g \o f" := (Map_compose f g)
  (at level 60, right associativity) : setoid_scope.

Class Injective `(f: Map X Y) : Prop :=
{ injective: forall x y, f x == f y -> x == y }.

Class Surjective `(f: Map X Y) : Prop :=
{ surjective: forall y, exists x, y == f x }.

Class Bijective `(f: Map X Y) : Prop := {
  bij_injective:> Injective f;
  bij_surjective:> Surjective f
}.

Lemma mapcomp_reduc : forall {X Y Z} {f g: Map Y Z} {h: Map X Y},
  Surjective h -> f \o h == g \o h -> f == g.
Proof.
  intros X Y Z f g h [Sh] Heq. simpl. intros x y Heq1.
  rewrite Heq1. destruct (Sh y) as [x0 Heq2].
  rewrite Heq2. now apply Heq.
Qed.

Lemma mapcomp_assoc {X Y Z W} {f: Map Z W} {g: Map Y Z} {h: Map X Y} :
  (f \o g) \o h == f \o g \o h.
Proof.
  intros. simpl. intros x y Heq. now rewrite Heq.
Qed.

Program Definition Image `(f: Map X Y) (A: SubSetoid X)
  : SubSetoid Y := [subsetoid of y | exists x, (A x) /\ y == f x].
Next Obligation.
  split. intros a b Heq. split; intros [x [Ax Heq1]]; exists x;
  split; try apply Ax; (now rewrite <-Heq || now rewrite Heq).
Defined.

Program Definition Preimage `(f: Map X Y) (B: SubSetoid Y)
  : SubSetoid X := [subsetoid of x | exists y, (B y) /\ y == f x].
Next Obligation.
  split. intros a b Heq. split; intros [y [By Heq1]]; exists y;
  split; try apply By; (now rewrite <-Heq || now rewrite Heq).
Defined.

Class Included {X} (A B: SubSetoid X) := 
{ included: forall (x:X), A x -> B x }.

Notation "A '<=' B" := (@Included _ A B) : setoid_scope.

Lemma included_transitive {X} : Transitive (@Included X).
Proof. split. intros a xa. apply H0, H, xa. Qed.
#[global]
Existing Instance included_transitive.

Program Definition SubSetoid_setoid {X:Setoid} :=
  [setoid by (fun A B => (A <= B) /\ (B <= A)) on SubSetoid X].
Next Obligation.
  split.
  - intros A. split; split; intros x Ax; apply Ax.
  - intros A B [AB BA]. split; (apply BA || apply AB).
  - intros A B C [AB BA] [BC CB]. split; split; intros x.
    + intros Ax. apply BC. now apply AB.
    + intros Cx. apply BA. now apply CB.
Defined.
Canonical Structure SubSetoid_setoid.

Program Definition inclusion `{B: SubSetoid A} : Map B A
  := map h => h.
Next Obligation. split. intros x y. now simpl. Defined.

Lemma inc_inj `{B: SubSetoid A} : Injective (@inclusion A B).
Proof. split. intros x y. now simpl. Qed.


Declare Scope alg_scope.
Open Scope alg_scope.

Class IsBinop (X:Setoid) (op: X -> X -> X) :=
{ binop_proper:> Proper ((==) ==> (==) ==> (==)) op }.

Structure Binop (X:Setoid) := {
  binop_op:> X -> X -> X;
  
  binop_prf:> IsBinop X binop_op
}.
#[global]
Existing Instance binop_prf.

Notation "[ 'Binop' 'by' f ]" := (@Build_Binop _ f _) : alg_scope.
Notation " 'binop' x , y 'in' A => m " := [Binop by fun (x y:A) => m]
  (at level 70, right associativity) : alg_scope.
Notation " 'binop' x , y => m " := [Binop by fun (x y:_) => m]
  (at level 70, right associativity) : alg_scope.

Class Associative `(op: Binop X) := {
  associative: 
    forall x y z, op x (op y z) == op (op x y) z 
}.

Class LIdentical `(op: Binop X) (e:X) :=
{ lidentical: forall x, op e x == x }.

Class RIdentical `(op: Binop X) (e:X) :=
{ ridentical: forall x, op x e == x }.

Class Identical `(op: Binop X) (e:X) := {
  identical_l:> LIdentical op e;
  identical_r:> RIdentical op e
}.
#[global]
Existing Instances identical_l identical_r.


Class IsMonoid (M:Setoid) (op: Binop M) (e: M) := {
  monoid_assoc:> Associative op;
  monoid_ident:> Identical op e
}.

Structure Monoid := {
  monoid_supp:> Setoid;
  monoid_op: Binop monoid_supp;
  monoid_id: monoid_supp;

  monoid_prf:> IsMonoid monoid_supp monoid_op monoid_id
}.
#[global]
Existing Instance monoid_prf.

Notation "[ 'monoid' 'by' op , id 'on' A ]" :=
  (@Build_Monoid A op id _) : alg_scope.
Notation "[ 'monoid 'by' op , id ]" :=
  [monoid by op, id on _] : alg_scope.

(* Program Definition Map_monoid := [monoid by ] *)


Class LInvertible `(op: Binop X) (e:X) (inv: Map X X) :=
{ linvertible: forall x, op (inv x) x == e }.

Class RInvertible `(op: Binop X) (e:X) (inv: Map X X) :=
{ rinvertible: forall x, op x (inv x) == e }.

Class Invertible `(op: Binop X) (e:X) (inv: Map X X) := {
  invertible_l:> LInvertible op e inv;
  invertible_r:> RInvertible op e inv
}.
#[global]
Existing Instances invertible_l invertible_r.


Class IsGroup 
      (supp:Setoid)
      (op: Binop supp)
      (inv: Map supp supp)
      (e:supp) := 
{
  grp_op_assoc:> Associative op;
  grp_id_ident_r:> RIdentical op e;
  grp_inv_invert_r:> RInvertible op e inv
}.

Structure Group :=
{
  grp_supp:> Setoid;
  grp_op: Binop grp_supp;
  grp_inv: Map grp_supp grp_supp;
  grp_id: grp_supp;

  grp_prf:> IsGroup grp_supp grp_op grp_inv grp_id
}.
#[global]
Existing Instance grp_prf.

Notation "[ 'group' 'by' op , inv , id 'on' A ]" :=
  (@Build_Group A op inv id _).
Notation "[ 'group' 'by' op , inv , id ]" :=
  [group by op, inv, id on _].

Notation "( * 'in' G )" := (@grp_op G) : alg_scope.
Notation "( * )" := ( * in _) : alg_scope.
Notation "g *_{ G } h" := (@grp_op G g h)
  (at level 60, right associativity) : alg_scope.
Notation "g * h" := (g *_{_} h) : alg_scope.
Notation "1_{ G }" := (@grp_id G) : alg_scope.
Notation "'1'" := 1_{_} : alg_scope.
Notation "(\! 'in' G ) " := (@grp_inv G) : alg_scope.
Notation "(\!)" := (\! in _) : alg_scope.
Notation "!_{ G } g " := (@grp_inv G g)
  (at level 30, right associativity) : alg_scope.
Notation "! g" := ( !_{_} g)
  (at level 30, right associativity) : alg_scope.

Lemma grp_id_ident_l : forall {G:Group}, LIdentical ( * in G) 1.
Proof.
  split. intros x.
  assert (1 * x == 1 * (x * 1)) as Heq0.
  { now rewrite ridentical. }
  assert (x * 1 == x * !x * !!x) as Heq1.
  { now rewrite <-(rinvertible (!x)), associative. }
  rewrite Heq0, Heq1, rinvertible, associative, ridentical.
  assert (1 == x * !x) as Heq2. { now rewrite rinvertible. }
  now rewrite Heq2, <-associative, rinvertible, ridentical.
Qed.
#[global]
Existing Instance grp_id_ident_l.

Lemma grp_inv_invert_l {G} : LInvertible ( * in G) 1 (\!).
Proof.
  split. intros x.
  assert (!x * x == !x * (x * !x) * !!x) as Heq0.
  { now rewrite associative, <-associative, rinvertible, ridentical. }
  now rewrite Heq0, rinvertible, ridentical, rinvertible.
Qed.
#[global]
Existing Instance grp_inv_invert_l.

Section GroupTheory.
  Context {G:Group}.
  Lemma grp_op_inj_r : forall {g x y:G},
    x * g == y * g -> x == y.
  Proof.
    intros g x y Heq.
    assert (x * (g * !g) == y * (g * !g)) as H.
    { now rewrite 2!associative, Heq. }
    now rewrite rinvertible, 2!ridentical in H.
  Qed.

  Lemma grp_op_inj_l : forall {g x y:G},
    g * x == g * y -> x == y.
  Proof.
    intros g x y Heq. 
    assert (!g * g * x == !g * g * y) as H.
    { now rewrite <-2!associative, Heq. }
    now rewrite linvertible, 2!lidentical in H.
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
    now rewrite associative, rinvertible, lidentical.
  Qed.

  Lemma grp_send_r : forall {g x y:G},
    x * g == y -> x == y * !g.
  Proof.
    intros g x y Heq.
    apply (grp_op_inj_r(g:=g)).
    now rewrite <-associative, linvertible, ridentical.
  Qed.
  
  Lemma grp_invinv : forall {x:G}, !!x == x.
  Proof.
    intros x.
    assert (!!x * !x == x * !x) as H.
    { now rewrite linvertible, rinvertible. }
    now apply grp_op_inj_r in H.
  Qed.

  Lemma grp_opinv : forall {x y:G},
    !(x * y) == !y * !x.
  Proof.
    intros x y. 
    rewrite <-(ridentical (!y * !x)), <-associative.
    apply grp_send_l, grp_send_l.
    now rewrite associative, rinvertible.
  Qed.

  Lemma grp_invid_id : !1_{G} == 1.
  Proof.
    rewrite <-(ridentical (!1)).
    symmetry; apply grp_send_l, lidentical.
  Qed.
End GroupTheory.


Class IsHomomorph {G H:Group} (f: Map G H) := {
  homomorph:
    forall {x y:G}, f (x * y) == (f x) * (f y)
}.

Structure Homomorph (G H:Group) := {
  hom_map:> Map G H;
  
  hom_prf:> IsHomomorph hom_map
}.
#[global]
Existing Instance hom_prf.

Notation "[ 'hom' 'by' f ]" :=
  (@Build_Homomorph _ _ [map by f] _) : alg_scope.
Notation " 'hom' x 'in' G => m " := [hom by fun (x:G) => m]
  (at level 70, right associativity) : alg_scope.
Notation " 'hom' x => m " := (hom x in _ => m)
  (at level 70, right associativity) : alg_scope.

Class IsIsomorph `(f: Homomorph G H) := {
  isomorph:> Bijective f
}.

Structure Isomorph (G H:Group):= {
  iso_map:> Homomorph G H;

  iso_prf:> IsIsomorph iso_map
}.
#[global]
Existing Instance iso_prf.
Notation "[ 'iso' 'by' f ]" :=
  (@Build_Isomorph _ _ [hom by f] _) : alg_scope.
Notation "'iso' x 'in' G => m " := [iso by fun (x:G) => m]
  (at level 70, right associativity) : alg_scope.
Notation "'iso' x => m " := (iso x in _ => m)
  (at level 70, right associativity) : alg_scope.


Section HomTheory.
  Context {G H:Group} {f: Homomorph G H}.
  Lemma hom_id : f 1 == 1.
  Proof.
    rewrite <-(rinvertible (f 1)).
    apply grp_send_r. now rewrite <-homomorph, ridentical.
  Qed.

  Lemma hom_inv : forall x, f (!x) == ! f x.
  Proof.
    intros x.
    rewrite <-(ridentical (!(f x))).
    apply grp_send_l.
    now rewrite <-homomorph, rinvertible, hom_id.
  Qed.
End HomTheory.


Class IsSubGroup (G:Group) (H: SubSetoid G) :=
{
  sg_ferm_op:
    forall {x y}, H x -> H y -> H (x * y);
  
  sg_ferm_inv:
    forall {x}, H x -> H (!x);
  
  sg_ferm_id: H 1
}.

Structure SubGroup (G:Group) := {
  sg_supp:> SubSetoid G;

  sg_prf:> IsSubGroup G sg_supp
}.
#[global]
Existing Instance sg_prf.

Notation "H '<-' G" := (@Build_SubGroup G H _)
  (at level 60, right associativity) : alg_scope.
Notation "[ 'subgroup' 'of' x 'in' G | P ] " :=
  ([subsetoid of x | P] <- G) : alg_scope.
Notation "[ 'subgroup' 'of' x | P ]" :=
  ([subgroup of x in _ | P]) : alg_scope.

Program Definition sg_as_group `(H:SubGroup G) :=
  [group by (binop x, y => x * y), (map x => !x), 1 on H].
Next Obligation.
  apply sg_ferm_op; (apply H1 || apply H0).
Defined.
Next Obligation.
  split. intros x1 y1 Heq x0 y0 Heq1. simpl. 
  simpl in Heq. simpl in Heq1. now rewrite Heq, Heq1.
Defined.
Next Obligation.
  apply sg_ferm_inv, H0.
Defined.
Next Obligation.
  split. intros x y. simpl. intros Heq.
  now rewrite Heq.
Defined.
Next Obligation.
  apply sg_ferm_id.
Defined.
Next Obligation.
  split.
  - split. intros x y z. simpl. apply associative.
  - split. intros x. simpl. apply ridentical.
  - split. intros x. simpl. apply rinvertible.
Defined.
Coercion sg_as_group : SubGroup >-> Group.





Class IsNormalSubGroup `(H: SubGroup G) := {
  normal:
    forall {g h}, H h -> H (g * h * !g)
}.

Structure NormalSubGroup (G:Group):= {
  nsg_supp:> SubGroup G;

  nsg_prf:> IsNormalSubGroup nsg_supp
}.
#[global]
Existing Instance nsg_prf.

Notation "H <| G" := (@Build_NormalSubGroup G H _)
  (at level 60, right associativity) : alg_scope.


Program Definition HomImage `(f: Homomorph G H):= 
  [subgroup of y | exists x, y == f x].
Next Obligation.
  split.
  - intros x y Heq. apply conj; 
    intros [z Heq1]; exists z; now rewrite <-Heq1, Heq.
Defined.
Next Obligation.
  split.
  - intros x y. simpl. intros [z1 Heq1] [z2 Heq2].
    exists (z1 * z2). now rewrite homomorph, Heq1, Heq2.
  - intros x [y Heq].
    exists (!y).
    now rewrite hom_inv, Heq.
  - exists 1. symmetry; apply hom_id.
Defined.

Program Definition confimg `(f: Homomorph G H) 
  : Homomorph G (HomImage f) := hom g => f g.
Next Obligation.
  now exists g.
Defined.
Next Obligation.
  split. intros x y Heq. simpl. now rewrite Heq.
Defined.
Next Obligation.
  split. intros x y. simpl. apply homomorph.
Defined.

Lemma confimg_surj `{f: Homomorph G H} : Surjective (confimg f).
Proof.
  split. intros [h [g Heq]]. simpl. now exists g.
Qed.
#[global]
Existing Instance confimg_surj.

Program Definition HomKernel `(f: Homomorph G H) :=
  [subgroup of x | f x == 1] <| G.
Next Obligation.
  split. intros g h. simpl. intros Heq. apply conj;
  intros Heq1; now rewrite <-Heq1, Heq.
Defined.
Next Obligation.
  split; simpl.
  - intros x y Heq1 Heq2.
    now rewrite homomorph, Heq1, Heq2, ridentical.
  - intros x Heq.
    now rewrite hom_inv, Heq, grp_invid_id.
  - apply hom_id.
Defined.
Next Obligation.
  split. simpl. intros g h Heq0.
  now rewrite 2!homomorph, Heq0, ridentical,
    <-homomorph, rinvertible, hom_id.
Defined.


Program Definition Coset `(H: SubGroup G) :=
  [setoid by (fun x y => H (x * !y)) on G].
Next Obligation.
  split.
  - intros x. rewrite rinvertible. apply sg_ferm_id.
  - intros x y Heq. apply sg_ferm_inv in Heq.
    now rewrite grp_opinv, grp_invinv in Heq.
  - intros x y z Hxy Hyz.
    pose (sg_ferm_op Hxy Hyz) as Hxz.
    now rewrite associative, <-(associative x (!y) y), 
      linvertible, ridentical in Hxz.
Defined.

Program Definition quotmap `{H: SubGroup G} : Map G (Coset H) :=
  map x => x.
Next Obligation.
  split. intros x y Heq. simpl. rewrite Heq, rinvertible.
  apply sg_ferm_id.
Defined.
(* Coercion _quotmap `{H: SubGroup G} : G -> Coset H := quotmap. *)

Lemma quotmap_surj `{H: SubGroup G} : Surjective (@quotmap G H).
Proof.
  split. intros g. simpl. exists g. 
  rewrite rinvertible. apply sg_ferm_id.
Defined.
#[global]
Existing Instance quotmap_surj.

Program Definition CosetGroup `(H: NormalSubGroup G) :=
  [group by (binop x, y => x * y), (map x => !x), 1 on Coset H].
Next Obligation.
  split. intros x0 y0. simpl. intros Heq0 x1 y1 Heq1.
  assert (H (x0 * x1 * !y1 * !x0)) as Heq2.
  { rewrite <-(associative _ _ (!y1)). now apply normal. }
  pose (sg_ferm_op Heq2 Heq0) as Heq3.
  rewrite associative, <-(associative _ (!x0) x0),
    linvertible, ridentical in Heq3.
  now rewrite grp_opinv, associative.
Defined.
Next Obligation.
  split. intros x y. simpl. intros Heq. rewrite <-grp_opinv.
  apply sg_ferm_inv. apply (normal(g := !y)) in Heq.
  now rewrite grp_invinv, associative, <-(associative _ (!y) y),
    linvertible, ridentical in Heq.
Defined.
Next Obligation.
  split; split.
  - intros x y z. simpl. rewrite associative, rinvertible.
    apply sg_ferm_id.
  - intros x. simpl. apply normal, sg_ferm_id.
  - intros x. simpl. rewrite grp_invid_id, ridentical, rinvertible.
    apply sg_ferm_id.
Defined.

Lemma quotmap_hom `{H: NormalSubGroup G} : 
  (@IsHomomorph G (CosetGroup H)) quotmap.
Proof. 
  split. intros x y. simpl. rewrite rinvertible. apply sg_ferm_id.
Qed.

Program Definition SubGroup_setoid {G:Group} :=
  [subsetoid of H in (@SubSetoid_setoid G) | IsSubGroup G H].
Next Obligation.
  split. intros H1 H2. simpl. intros [H1H2 H2H1]. split;
  intros [Hfop Hfinv Hfid]; split; try intros x y Hx Hy;
  try intros x Hx; try apply H1H2;
  try apply Hfid; try apply Hfop; try apply Hfinv;
  try apply H2H1; try apply Hx; try apply Hy;
  try apply Hfid; try apply Hfop; try apply Hfinv;
  try apply H1H2; try apply Hx; try apply Hy.
Defined.

Section FundHom.
  Context {G H:Group} (f: Homomorph G H)
    (N := HomKernel f) (G_N := CosetGroup N).

  Program Definition Iso1 : Isomorph G_N (HomImage f):=
    iso x => f x.
  Next Obligation.
    now exists x.
  Defined.
  Next Obligation.
    split. intros x y. simpl. intros Heq.
    rewrite homomorph, hom_inv in Heq.
    apply grp_send_r in Heq.
    now rewrite grp_invinv, lidentical in Heq.
  Defined.
  Next Obligation.
    split. intros x y. simpl. apply homomorph.
  Defined.
  Next Obligation.
    split; split; split.
    - intros x y. simpl. intros Heq.
      rewrite homomorph, hom_inv.
      symmetry; apply grp_send_r.
      now rewrite lidentical.
    - intros [y [x Heq]]. simpl. now exists x.
  Defined.

  Lemma Iso1comp_proper :
    f == inclusion \o Iso1 \o quotmap in (Map_setoid G H).
  Proof. intros x y Heq. simpl. now rewrite Heq. Qed.

  Lemma Iso1_identical : forall (psi: Homomorph G_N H), 
    f == psi \o quotmap in (Map_setoid G H) ->
    psi == inclusion \o Iso1 in (Map_setoid G_N H).
  Proof.
    intros psi Hiso x y Heq. rewrite Heq.
    rewrite Iso1comp_proper in Hiso.
    rewrite <-mapcomp_assoc in Hiso.
    pose (mapcomp_reduc _ Hiso) as Heq2.
    symmetry. now apply Heq2.
  Qed.
End FundHom.

Section CorrespSubGroup.
  Context {G:Group} {N: NormalSubGroup G} (G_N := CosetGroup N).

  Program Definition corresp_quotsg_to_sg 
    : Map (@SubGroup_setoid G_N)
      [subsetoid of K in (@SubGroup_setoid G) | N <= K]
    := map H => (Preimage quotmap H).
  Next Obligation.
    split. intros H1 H2. simpl. intros [H1H2 H2H1]. split; intros NH.
    - apply (transitivity NH H1H2).
    - apply (transitivity NH H2H1).
  Defined.
  Next Obligation.
    pose (Build_SubGroup G_N H H0) as grpH. split. 
    - intros g h. simpl. intros [y0 [Hy0 Heq0]] [y1 [Hy1 Heq1]].
      exists (y0 * y1). split. 
      + apply (sg_ferm_op(H := grpH) Hy0 Hy1).
      + apply (normal(g := g)) in Heq1.
        pose (sg_ferm_op Heq0 Heq1) as Heq2.
        rewrite 3!associative, <-(associative _ (!g)),
          linvertible, ridentical in Heq2.
        now rewrite grp_opinv, associative.
    - intros x. simpl. intros [y [Hy Heq]].
      exists (!y). split.
      + apply (sg_ferm_inv(H := grpH) Hy).
      + rewrite <-grp_opinv. apply sg_ferm_inv.
        apply (normal(g := !x)) in Heq.
        now rewrite associative, <-associative,
          rinvertible, ridentical in Heq.
    - simpl. exists 1. split.
      + apply (sg_ferm_id(H := grpH)).
      + rewrite grp_invid_id, ridentical. 
        apply sg_ferm_id.
  Defined.
  Next Obligation.
    pose (Build_SubGroup G_N H H0) as grpH.
    split. simpl. intros x Nx. exists x. split.
    - assert (x == 1 in G_N) as Hid. 
      { simpl. now rewrite grp_invid_id, ridentical. }
      rewrite Hid. apply (sg_ferm_id(H := grpH)).
    - rewrite rinvertible. apply sg_ferm_id.
  Defined.

  Program Definition corresp_sg_to_quotsg
    : Map [subsetoid of K in (@SubGroup_setoid G) | N <= K]
      (@SubGroup_setoid G_N)
    := map K => Image quotmap K.
  Next Obligation.
    split. intros SA SB. simpl. intros [[AB] [BA]]. split; split;
    intros g [gN [SgN Heq_g]]; simpl; simpl in Heq_g;
    exists gN; split; try apply Heq_g.
    - apply AB, SgN.
    - apply BA, SgN.
  Defined.
  Next Obligation.
    split. intros SA SB. simpl. intros [AB BA]. split; intros NS.
    - apply (transitivity NS AB).
    - apply (transitivity NS BA).
  Defined.
  Next Obligation.
    split; simpl.
    - intros x y [g [Kg Heq0]] [h [Kh Heq1]]. exists (g * h). split.
      + apply (sg_ferm_op Kg Kh).
      + rewrite grp_opinv, <-lidentical, <-(rinvertible g).
        rewrite 3!associative, <-4!(associative),
          4!(associative _ _ (!g)). apply normal.
        apply (normal(g := !g)) in Heq0.
        rewrite grp_invinv, associative, <-associative,
          linvertible, ridentical in Heq0.
        rewrite associative. apply (sg_ferm_op Heq0 Heq1).
    - intros g [h [Kh Nh]]. exists (!h). split.
      + apply sg_ferm_inv, Kh.
      + rewrite <-grp_opinv. apply sg_ferm_inv.
        apply (normal(g := !h)) in Nh.
        now rewrite grp_invinv, associative, <-associative,
          linvertible, ridentical in Nh.
    - exists 1. rewrite grp_invid_id, ridentical. split;
      apply sg_ferm_id.
  Defined.
  Next Obligation.
    split. intros A B. simpl. intros [[AB] [BA]]. split; split; 
    intros x; simpl; intros [y [Sy Heq]]; exists y; split;
    try apply Heq.
    - apply AB, Sy.
    - apply BA, Sy.
  Defined.

  Lemma corresp_comp_id_sg : 

Close Scope alg_scope.
Close Scope setoid_scope.

