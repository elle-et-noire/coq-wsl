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

Notation "'std' 'by' P 'on' A " := (@Build_Setoid A P _)
  (at level 100, P at next level, no associativity) : setoid_scope.
Notation "'std' 'by' P" := (std by P on _)
  (at level 100, no associativity) : setoid_scope.
Notation "( == 'in' A )" := (setoid_equal A)
  (at level 0, format "( == 'in' A )").
Notation "x == y 'in' A" := (setoid_equal A x y)
  (at level 70, y at next level, no associativity).
Notation "(==)" := (== in _).
Notation "x == y" := (x == y in _)
  (at level 70, no associativity) : setoid_scope.
Notation typeof := setoid_carrier.

Program Definition eqSetoid (X:Type) := std by @eq X.

Program Definition functionSetoid (X Y:Type) : Setoid :=
  std by `(forall x, f x = g x) on (X -> Y).
Next Obligation. split; intros x; congruence. Defined.
Canonical Structure functionSetoid.

Program Definition PropSetoid := std by iff.
Canonical Structure PropSetoid.

Inductive empty : Type := .
Program Definition emptySetoid :=
  std by fun e e' => match e, e' with end on empty.
Next Obligation. split; intros x; case x. Qed.

Program Definition unitSetoid := std by fun _ _ => True on unit.
Next Obligation. split; intros H; tauto. Qed.

Definition DirectProduct_eq {A B:Setoid} (a b: A * B) :=
   fst a == fst b /\ snd a == snd b.

Program Definition DirectProductSetoid (A B:Setoid) :=
  std by DirectProduct_eq on A * B.
Next Obligation.
  split.
  - intros a. now split.
  - intros a b [H1 H2]. split; now (rewrite H1 || rewrite H2).
  - intros a b c [H1 H2] [H3 H4]. split;
    now (rewrite H1, H3 || rewrite H2, H4).
Defined.
Canonical Structure DirectProductSetoid.
Notation "[( A , B )]" := (DirectProductSetoid A B)
  : setoid_scope.


Class IsSubsetoid (X:Setoid) (conf: typeof X -> Prop) := {
  subconf_proper:> Proper ((==) ==> (==)) conf
}.

Structure Subsetoid (X:Setoid) : Type := {
  sub_conf:> typeof X -> Prop;

  sub_prf:> IsSubsetoid X sub_conf
}.
#[global]
Existing Instance sub_prf.

Notation "'sstd' 'by' C 'on' A" := (@Build_Subsetoid A C _)
  (at level 100, C at next level, no associativity) : setoid_scope.
Notation "'sstd' 'by' C" := (sstd by C on _)
  (at level 100, no associativity) : setoid_scope.
Notation "[  x 'in' A | P  ]" := (sstd by (fun x => P) on A)
  : setoid_scope.
Notation "[  x | P  ]" := [x in _ | P]
  : setoid_scope.

Program Coercion Subsetoid_toSetoid `(B: Subsetoid A) :=
  std by (== in A) on { x | B x }.
Next Obligation.
  split.
  - now intros x.
  - intros x y Heq. now symmetry.
  - intros x y z Heq1 Heq2. now rewrite Heq1.
Defined.
Notation "[|  B  |]" := (@Subsetoid_toSetoid _ B) : setoid_scope.


Program Definition selfSubsetoid (A:Setoid) := [ _ | True ].
Next Obligation. split. now intros x y Heq. Defined.
Notation "[{  A  }]" := (@selfSubsetoid A) : setoid_scope.

Program Definition emptySubsetoid {A:Setoid} := [ _ | False ].
Next Obligation. split. now intros x y Heq. Defined.
Notation "[{ } 'in' A  ]" := (@emptySubsetoid A) : setoid_scope.
Notation "[{ }]" := [{} in _] : setoid_scope.

Program Definition unitSubsetoid {A:Setoid} (a:A) 
  := [ x | x == a ].
Next Obligation.
  split. intros x y Heq. split; intros Heq1; now rewrite <-Heq1.
Defined.
Notation "[  $ a 'in' A  ]" := (@unitSubsetoid A a)
  : setoid_scope.
Notation "[  $ a  ]" := [ $ a in _]
  : setoid_scope.


Class Included {X} (A B: Subsetoid X) := {
  included: forall (x: typeof X), A x -> B x
}.
Notation "A '<=' B" := (@Included _ A B) : setoid_scope.

Lemma included_trans {X} : Transitive (@Included X).
Proof. split. intros a xa. apply H0, H, xa. Qed.
#[global]
Existing Instance included_trans.

Program Definition SubsetoidSetoid (X:Setoid) :=
  std by fun A B => A <= B /\ B <= A on Subsetoid X.
Next Obligation.
  split.
  - intros A. split; split; intros x Ax; apply Ax.
  - intros A B [AB BA]. split; (apply BA || apply AB).
  - intros A B C [AB BA] [BC CB]. split; split; intros x.
    + intros Ax. apply BC. now apply AB.
    + intros Cx. apply BA. now apply CB.
Defined.
Canonical Structure SubsetoidSetoid.

Class IsMap {X Y:Setoid} (f: X -> Y) := {
  map_proper:> Proper ((==) ==> (==)) f
}.

Structure Map (X Y:Setoid) : Type := {
  map_fun:> typeof X -> typeof Y;

  map_prf:> IsMap map_fun
}.
#[global]
Existing Instance map_prf.

Notation "'map' 'by' f" := (@Build_Map _ _ f _)
  (at level 100, no associativity) : setoid_scope.
Notation " 'map' x 'in' X => m " := (map by fun (x:X) => m)
  (at level 100, x, X at next level, no associativity)
   : setoid_scope.
Notation " 'map' x => m " := (map x in _ => m)
  (at level 100, x at next level, no associativity) : setoid_scope.

Program Definition Map_id {X:Setoid} : Map X X := map x => x.
Next Obligation. split. intros x y Heq. apply Heq. Defined.

Program Definition MapSetoid (X Y: Setoid) : Setoid :=
  std by ((==) ==> (==))%signature on Map X Y.
Next Obligation.
  split.
  - intros f x y Heq. now rewrite Heq. 
  - intros f g Heq1 x y Heq2. now rewrite (Heq1 y x (symmetry Heq2)).
  - intros f g h Heq1 Heq2 x y Heq3. 
    now rewrite (Heq1 x y Heq3), <-(Heq2 x y Heq3), Heq3.
Defined.
Canonical Structure MapSetoid.

Program Definition Map_compose {X Y Z} (f: Map X Y) (g: Map Y Z)
  : Map X Z := map x => g (f x).
Next Obligation. split. intros x y Heq. now rewrite Heq. Defined.
Notation "g \o f" := (Map_compose f g)
  (at level 60, right associativity) : setoid_scope.


Class Injective `(f: Map X Y) : Prop := {
  injective: forall x y, f x == f y -> x == y
}.

Class Surjective `(f: Map X Y) : Prop := {
  surjective: forall y, exists x, y == f x
}.

Class Bijective `(f: Map X Y) : Prop := {
  bij_injective:> Injective f;
  bij_surjective:> Surjective f
}.

Lemma Map_reduc : forall {X Y Z} {f g: Map Y Z} {h: Map X Y},
  Surjective h -> f \o h == g \o h -> f == g.
Proof.
  intros X Y Z f g h [Sh] Heq. simpl. intros x y Heq1.
  rewrite Heq1. destruct (Sh y) as [x0 Heq2].
  rewrite Heq2. now apply Heq.
Qed.

Lemma Map_assoc {X Y Z W} {f: Map Z W} {g: Map Y Z} {h: Map X Y} :
  (f \o g) \o h == f \o g \o h.
Proof. intros. simpl. intros x y Heq. now rewrite Heq. Qed.


Program Definition Image `(f: Map X Y)
  : Map (Subsetoid X) (Subsetoid Y)
  := map A => [ y | exists x, A x /\ y == f x ].
Next Obligation.
  split. intros a b Heq. split; intros [x [Ax Heq1]]; exists x;
  split; try apply Ax; (now rewrite <-Heq || now rewrite Heq).
Defined.
Next Obligation.
  split. intros A B. simpl. intros [[AB] [BA]]. split; split;
  intros y [x [Ax E0]]; simpl; exists x; split; try apply E0.
  - apply AB, Ax.
  - apply BA, Ax.
Defined.

Program Definition Preimage `(f: Map X Y)
  : Map (Subsetoid Y) (Subsetoid X)
  := map B => [ x | B (f x) ].
Next Obligation. split. intros a b Heq. now rewrite Heq. Defined.
Next Obligation.
  split. intros A B [AB BA]. split; split; simpl;
  intros x Hf; now (apply AB || apply BA).
Defined.


Program Definition inclusion `{B: Subsetoid A} : Map B A
  := map h => h.
Next Obligation. split. intros x y. now simpl. Defined.

Lemma inclusion_inj `{B: Subsetoid A} : Injective (@inclusion A B).
Proof. split. intros x y. now simpl. Qed.


Declare Scope alg_scope.
Open Scope alg_scope.

Class IsBinop (X:Setoid) (op: X -> X -> X) := {
  binop_proper:> Proper ((==) ==> (==) ==> (==)) op 
}.

Structure Binop (X:Setoid) := {
  binop_op:> X -> X -> X;
  
  binop_prf:> IsBinop X binop_op
}.
#[global]
Existing Instance binop_prf.

Notation "'binop' 'by' f" := (@Build_Binop _ f _)
  (at level 100, no associativity) : alg_scope.
Notation " 'binop' x , y 'in' A => m " := (binop by fun (x y:A) => m)
  (at level 100, x, y, A at next level, no associativity) : alg_scope.
Notation " 'binop' x , y => m " := (binop by fun (x y:_) => m)
  (at level 100, x, y at next level, no associativity) : alg_scope.


Class Associative `(op: Binop X) := {
  associative:
    forall x y z, op x (op y z) == op (op x y) z 
}.

Class LIdentical `(op: Binop X) (e:X) := {
  lidentical: forall x, op e x == x
}.

Class RIdentical `(op: Binop X) (e:X) := {
  ridentical: forall x, op x e == x
}.

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

Notation "'mnd' 'by' op , id 'on' A" := (@Build_Monoid A op id _)
  (at level 100, op, id at next level, no associativity) : alg_scope.
Notation "'mnd' 'by' op , id" := (mnd by op, id on _)
  (at level 100, op, id at next level, no associativity) : alg_scope.


Class LInvertible `(op: Binop X) (e:X) (inv: Map X X) := {
  linvertible: forall x, op (inv x) x == e
}.

Class RInvertible `(op: Binop X) (e:X) (inv: Map X X) := {
  rinvertible: forall x, op x (inv x) == e
}.

Class Invertible `(op: Binop X) (e:X) (inv: Map X X) := {
  invertible_l:> LInvertible op e inv;
  invertible_r:> RInvertible op e inv
}.
#[global]
Existing Instances invertible_l invertible_r.


Class IsGroup (supp:Setoid) (op: Binop supp) 
              (inv: Map supp supp) (e:supp) :=
{
  grp_op_assoc:> Associative op;
  grp_id_ident_r:> RIdentical op e;
  grp_inv_invert_r:> RInvertible op e inv
}.

Structure Group := {
  grp_supp:> Setoid;
  grp_op: Binop grp_supp;
  grp_inv: Map grp_supp grp_supp;
  grp_id: grp_supp;

  grp_prf:> IsGroup grp_supp grp_op grp_inv grp_id
}.
#[global]
Existing Instance grp_prf.

Notation "'grp' 'by' op , inv , id 'on' A" :=
  (@Build_Group A op inv id _)
  (at level 100, op, inv, id at next level, no associativity) : alg_scope.
Notation "'grp' 'by' op , inv , id" := (grp by op, inv, id on _)
  (at level 100, op, inv, id at next level, no associativity) : alg_scope.
Notation "( * 'in' G  )" := (@grp_op G) : alg_scope.
Notation "( * )" := ( * in _ ) : alg_scope.
Notation "g *_{ G } h" := (@grp_op G g h)
  (at level 40, left associativity) : alg_scope.
Notation "g * h" := (g *_{_} h) : alg_scope.
Notation "1_{ G }" := (@grp_id G) : alg_scope.
Notation "'1'" := 1_{_} : alg_scope.
Notation "( ! 'in' G  ) " := (@grp_inv G) : alg_scope.
Notation "( ! )" := ( ! in _) : alg_scope.
Notation "!_{ G } g " := (@grp_inv G g)
  (at level 35, right associativity) : alg_scope.
Notation "! g" := ( !_{_} g)
  (at level 35, right associativity) : alg_scope.

Lemma grp_id_ident_l : forall {G:Group}, LIdentical ( * in G ) 1.
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

Lemma grp_inv_invert_l {G} : LInvertible ( * in G) 1 ( ! ).
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
  Lemma opinj_r : forall {g x y:G},
    x * g == y * g -> x == y.
  Proof.
    intros g x y Heq.
    assert (x * (g * !g) == y * (g * !g)) as H.
    { now rewrite 2!associative, Heq. }
    now rewrite rinvertible, 2!ridentical in H.
  Qed.

  Lemma opinj_l : forall {g x y:G},
    g * x == g * y -> x == y.
  Proof.
    intros g x y Heq. 
    assert (!g * g * x == !g * g * y) as H.
    { now rewrite <-2!associative, Heq. }
    now rewrite linvertible, 2!lidentical in H.
  Qed.

  Lemma send_l : forall {g x y:G},
    g * x == y -> x == !g * y.
  Proof.
    intros g x y Heq.
    apply (opinj_l(g:=g)).
    now rewrite associative, rinvertible, lidentical.
  Qed.

  Lemma send_r : forall {g x y:G},
    x * g == y -> x == y * !g.
  Proof.
    intros g x y Heq.
    apply (opinj_r(g:=g)).
    now rewrite <-associative, linvertible, ridentical.
  Qed.

  Lemma invinv : forall {x:G}, !!x == x.
  Proof.
    intros x.
    assert (!!x * !x == x * !x) as H.
    { now rewrite linvertible, rinvertible. }
    now apply opinj_r in H.
  Qed.

  Lemma opinv : forall {x y:G},
    !(x * y) == !y * !x.
  Proof.
    intros x y. 
    rewrite <-(ridentical (!y * !x)), <-associative.
    apply send_l, send_l.
    now rewrite associative, rinvertible.
  Qed.

  Lemma invid : !1_{G} == 1.
  Proof.
    rewrite <-(ridentical (!1)).
    symmetry; apply send_l, lidentical.
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

Notation "'hom' 'besides' 'map' f" := (@Build_Homomorph _ _ f _)
  (at level 100, no associativity) : alg_scope.
Notation "'hom' 'by' f " := (hom besides map (map by f))
  (at level 100, no associativity) : alg_scope.
Notation " 'hom' x 'in' G => m " := (hom by fun (x:G) => m)
  (at level 100, x, G at next level, no associativity) : alg_scope.
Notation " 'hom' x => m " := (hom x in _ => m)
  (at level 100, x at next level, no associativity) : alg_scope.

Class IsIsomorph `(f: Homomorph G H) := {
  isomorph:> Bijective f
}.

Structure Isomorph (G H:Group):= {
  iso_map:> Homomorph G H;

  iso_prf:> IsIsomorph iso_map
}.
#[global]
Existing Instance iso_prf.

Notation "'iso' 'besides' 'hom' f" := (@Build_Isomorph _ _ f _)
  (at level 100, no associativity) : alg_scope.
Notation "'iso' 'besides' 'map' f" := (iso besides hom (hom besides map f))
  (at level 100, no associativity) : alg_scope.
Notation "'iso' 'by' f" := (iso besides hom (hom by f))
  (at level 100, no associativity) : alg_scope.
Notation "'iso' x 'in' G => m " := (iso by fun (x:G) => m)
  (at level 100, x, G at next level, no associativity) : alg_scope.
Notation "'iso' x => m " := (iso x in _ => m)
  (at level 100, x at next level, no associativity) : alg_scope.
Notation "G ~= H" := (Isomorph G H)
  (at level 95, right associativity) : alg_scope.

Program Definition Hom_compose {X Y Z:Group}
  (f: Homomorph X Y) (g: Homomorph Y Z)
  : Homomorph X Z := hom besides map (g \o f).
Next Obligation.
  split. intros x y. simpl. now rewrite 2!homomorph.
Defined.
Notation "g 'hom\o' f" := (Hom_compose f g)
  (at level 60, right associativity) : alg_scope.

Program Definition Iso_compose {X Y Z:Group}
  (f: Isomorph X Y) (g: Isomorph Y Z)
  : Isomorph X Z := iso besides hom (g hom\o f).
Next Obligation.
  split; split; split; simpl.
  - intros x y Heq. now apply injective, injective in Heq.
  - intros y. destruct (surjective y). destruct (surjective x).
    exists x0. now rewrite <-H0, <-H.
Defined.
Notation "g 'iso\o' f" := (Iso_compose f g)
  (at level 60, right associativity) : alg_scope.


Section HomTheory.
  Context {G H:Group} {f: Homomorph G H}.
  Lemma hom_id : f 1 == 1.
  Proof.
    rewrite <-(rinvertible (f 1)).
    apply send_r. now rewrite <-homomorph, ridentical.
  Qed.

  Lemma hom_inv : forall x, f (!x) == !(f x).
  Proof.
    intros x.
    rewrite <-(ridentical (!(f x))).
    apply send_l.
    now rewrite <-homomorph, rinvertible, hom_id.
  Qed.
End HomTheory.


Class IsSubgroup (G:Group) (H: Subsetoid G) := {
  ferm_op:
    forall {x y}, H x -> H y -> H (x * y);  
  ferm_inv:
    forall {x}, H x -> H (!x);
  ferm_id: H 1
}.

Structure Subgroup (G:Group) := {
  sg_supp:> Subsetoid G;

  sg_prf:> IsSubgroup G sg_supp
}.
#[global]
Existing Instance sg_prf.

Arguments sg_supp {_} _.

Notation "H '<-' G" := (IsSubgroup G H)
  (at level 70, no associativity) : alg_scope.
Notation "H <<- G" := (@Build_Subgroup G H _)
  (at level 70, no associativity) : alg_scope.

Program Coercion Subgroup_toGroup `(H:Subgroup G) :=
  grp by (binop x, y => x * y), (map x => !x), 1 on H.
Next Obligation. apply ferm_op; (apply H1 || apply H0). Defined.
Next Obligation.
  split. intros x1 y1 Heq x0 y0 Heq1. simpl.
  simpl in Heq. simpl in Heq1. now rewrite Heq, Heq1.
Defined.
Next Obligation. apply ferm_inv, H0. Defined.
Next Obligation.
  split. intros x y. simpl. intros Heq. now rewrite Heq.
Defined.
Next Obligation. apply ferm_id. Defined.
Next Obligation.
  split.
  - split. intros x y z. simpl. apply associative.
  - split. intros x. simpl. apply ridentical.
  - split. intros x. simpl. apply rinvertible.
Defined.
Notation "<|  H  |>" := (@Subgroup_toGroup _ H).

Class IsNormalSubgroup `(H: Subgroup G) := {
  normal:
    forall {g h}, H h -> H (g * h * !g)
}.

Structure NormalSubgroup (G:Group):= {
  nsg_supp:> Subgroup G;

  nsg_prf:> IsNormalSubgroup nsg_supp
}.
#[global]
Existing Instance nsg_prf.

Notation "H <| G" := (@IsNormalSubgroup G H)
  (at level 70, no associativity) : alg_scope.
Notation "H <<| G" :=
  (@Build_NormalSubgroup G H _)
  (at level 70, no associativity) : alg_scope.
Notation "H <<-| G" :=
  (@Build_NormalSubgroup G (H <<- G) _)
  (at level 70, no associativity) : alg_scope.


Program Definition GroupableSubsetoid (G:Group) :=
  [ H in Subsetoid G | H <- G].
Next Obligation.
  split. intros H1 H2. simpl. intros [H1H2 H2H1]. split;
  intros [Hfop Hfinv Hfid]; split; try intros x y Hx Hy;
  try intros x Hx; try apply H1H2;
  try apply Hfid; try apply Hfop; try apply Hfinv;
  try apply H2H1; try apply Hx; try apply Hy;
  try apply Hfid; try apply Hfop; try apply Hfinv;
  try apply H1H2; try apply Hx; try apply Hy.
Defined.
Notation "[ | <- G  ]" := (@GroupableSubsetoid G).

Program Definition SubgroupSetoid (G:Group) :=
  std by (== in Subsetoid G) on Subgroup G.
Next Obligation.
  split; try now intros x.
  intros x y z [Hxy Hyx] [Hyz Hzy]. split.
  - apply (transitivity Hxy Hyz).
  - apply (transitivity Hzy Hyx).
Defined.
Canonical Structure SubgroupSetoid.
Notation "[ <> | <- G  ]" := (SubgroupSetoid G). 

Program Definition GroupableSubsetoid_toSubgroup {G:Group}
  : Map [ | <- G ] [ <> | <- G ]
  := map H => H <<- G.
Next Obligation. split. intros A B. simpl. intuition. Defined.
Notation "H <<[]- G" :=
  (@GroupableSubsetoid_toSubgroup G H)
  (at level 70, no associativity) : alg_scope.

Program Definition Subgroup_toGroupableSetoid {G:Group}
  : Map [ <> | <- G ] [ | <- G ]
  := map H => sg_supp H.
Next Obligation. intuition. Defined.
Next Obligation. split. intros A B. simpl. intuition. Defined.
Notation "H [<-] G" :=
  (@Subgroup_toGroupableSetoid G H)
  (at level 70, no associativity) : alg_scope.


Program Definition selfSubgroup (G:Group) : Subgroup G
  := [{ G }] <<- G.
Next Obligation. split; simpl; intros; trivial. Defined.
Notation "<{ G }>" := (selfSubgroup G).

Program Definition idNormalSubgroup {G:Group}
  : NormalSubgroup G := [$1] <<-| G.
Next Obligation. 
  split; simpl; intuition.
  - rewrite H, H0. apply lidentical.
  - rewrite H. apply invid.
Defined.
Next Obligation.
  split. intros g h. simpl. intros Heq.
  now rewrite Heq, ridentical, rinvertible.
Defined.
Notation "< 1 'in' G  >" := (@idNormalSubgroup G)
  (at level 0, G at next level)
  : alg_scope.
Notation "<1>" := < 1 in _ >
  : alg_scope.

Program Definition Subgroup_inSubgroup {G:Group} (N H: Subgroup G)
  : Subgroup H := [ n | N n ] <<- H.
Next Obligation. split. intros g h. simpl. intros Heq. now rewrite Heq. Defined.
Next Obligation.
  split; simpl.
  - intros x y Nx Ny. apply (ferm_op Nx Ny).
  - intros x Nx. apply (ferm_inv Nx).
  - apply ferm_id. 
Defined.
Notation "<  N 'inside' H   >" := (@Subgroup_inSubgroup _ N H)
  (at level 0, N, H at next level)
  : alg_scope.

Program Definition NormalSubgroup_inSubgroup {G:Group} (N: NormalSubgroup G) (H: Subgroup G)
  : NormalSubgroup H := < N inside H > <<| H.
Next Obligation. split. intros g h. simpl. apply normal. Defined.
Notation "<|  N 'inside' H   |>" := (@NormalSubgroup_inSubgroup _ N H)
  (at level 0, N, H at next level) : alg_scope.

Program Definition HomImage `(f: Homomorph G H)
  : Map (Subgroup G) (Subgroup H)
  := map A => GroupableSubsetoid_toSubgroup ((Image f) (Subgroup_toGroupableSetoid A)).
Next Obligation.
  split.
  - intros x y. simpl. intros [z1 [Az1 Heq1]] [z2 [Az2 Heq2]].
    exists (z1 * z2). split.
    + apply (ferm_op Az1 Az2).
    + now rewrite homomorph, Heq1, Heq2.
  - intros x [y [Ay Heq]].
    exists (!y). split.
    + apply ferm_inv, Ay.
    + now rewrite hom_inv, Heq.
  - exists 1. split.
    + apply ferm_id.
    + symmetry; apply hom_id.
Defined.
Next Obligation.
  split. intros A B. simpl. intros [[AB] [BA]]. split; split;
  intros x; simpl; intros [g [Ag E]]; exists g; split;
  try apply E.
  - apply AB, Ag.
  - apply BA, Ag.
Defined.

Program Definition HomKernel `(f: Homomorph G H) :=
  Preimage f [$1] <<-| G.
Next Obligation.
  split; simpl.
  - intros x y Heq1 Heq2.
    now rewrite homomorph, Heq1, Heq2, ridentical.
  - intros x Heq.
    now rewrite hom_inv, Heq, invid.
  - apply hom_id.
Defined.
Next Obligation.
  split. simpl. intros g h Heq0.
  now rewrite 2!homomorph, Heq0, ridentical,
    <-homomorph, rinvertible, hom_id.
Defined.


Program Definition Coset `(H: Subgroup G) :=
  std by fun x y => H (x * !y) on G.
Next Obligation.
  split.
  - intros x. rewrite rinvertible. apply ferm_id.
  - intros x y Heq. apply ferm_inv in Heq.
    now rewrite opinv, invinv in Heq.
  - intros x y z Hxy Hyz.
    pose (ferm_op Hxy Hyz) as Hxz.
    now rewrite associative, <-(associative x (!y) y), 
      linvertible, ridentical in Hxz.
Defined.

Corollary coset_eq `{H: Subgroup G} : forall {g h:G},
  H (g * !h) -> g == h in Coset H.
Proof. intros g h Heq. apply Heq. Qed.

Program Definition quotmap `{H: Subgroup G} : Map G (Coset H) :=
  map x => x.
Next Obligation.
  split. intros x y Heq. simpl. rewrite Heq, rinvertible.
  apply ferm_id.
Defined.

Lemma quotmap_surj `{H: Subgroup G} : Surjective (@quotmap G H).
Proof.
  split. intros g. simpl. exists g. 
  rewrite rinvertible. apply ferm_id.
Defined.
#[global]
Existing Instance quotmap_surj.

Program Definition CosetGroup `(H: NormalSubgroup G) :=
  grp by (binop x, y => x * y), (map x => !x), 1 on Coset H.
Next Obligation.
  split. intros x0 y0. simpl. intros Heq0 x1 y1 Heq1.
  assert (H (x0 * x1 * !y1 * !x0)) as Heq2.
  { rewrite <-(associative _ _ (!y1)). now apply normal. }
  pose (ferm_op Heq2 Heq0) as Heq3.
  rewrite associative, <-(associative _ (!x0) x0),
    linvertible, ridentical in Heq3.
  now rewrite opinv, associative.
Defined.
Next Obligation.
  split. intros x y. simpl. intros Heq. rewrite <-opinv.
  apply ferm_inv. apply (normal(g := !y)) in Heq.
  now rewrite invinv, associative, <-(associative _ (!y) y),
    linvertible, ridentical in Heq.
Defined.
Next Obligation.
  split; split.
  - intros x y z. simpl. rewrite associative, rinvertible.
    apply ferm_id.
  - intros x. simpl. apply normal, ferm_id.
  - intros x. simpl. rewrite invid, ridentical, rinvertible.
    apply ferm_id.
Defined.
Notation "<  G / N  >" := (@CosetGroup G N)
  (at level 0, G, N at next level) : alg_scope.

Program Definition quothom `{H: NormalSubgroup G}
  : Homomorph G (CosetGroup H) := (hom g => (quotmap g)).
Next Obligation. apply (map_prf _ _ quotmap). Defined.
Next Obligation.
  split. intros x y. simpl. rewrite rinvertible. apply ferm_id.
Defined.


Section FundHom.
  Context {G H:Group} (f: Homomorph G H)
    (N := HomKernel f) (G_N := CosetGroup N).

  Program Definition Iso1_kernel {A: NormalSubgroup G} {B: Subgroup H}
    (EAN: (A == N in SubgroupSetoid G))
    (EBI: (B == HomImage f <{ G }> in SubgroupSetoid H))
    : Isomorph (CosetGroup A) B :=
    iso x => f x.
  Next Obligation. apply H1. simpl. now exists x. Defined.
  Next Obligation.
    split. intros x y. simpl. intros Heq. apply i1 in Heq. simpl in Heq.
    rewrite homomorph, hom_inv in Heq.
    apply send_r in Heq.
    now rewrite invinv, lidentical in Heq.
  Defined.
  Next Obligation. split. intros x y. simpl. apply homomorph. Defined.
  Next Obligation.
    split; split; split.
    - intros x y. simpl. intros Heq. apply i2. simpl.
      rewrite homomorph, hom_inv.
      symmetry; apply send_r.
      now rewrite lidentical.
    - simpl. intros [y By]. simpl. destruct i as [i].
      simpl in i. destruct (i _ By) as [x [_ E]].
      now exists x.
  Defined.

  Program Definition Iso1
    : Isomorph G_N (HomImage f <{ G }>) 
    := Iso1_kernel _ _.
  Next Obligation. split; split; intuition. Defined.
  Next Obligation. split; split; intuition. Defined.

  Lemma Iso1comp_proper :
    f == inclusion \o Iso1 \o quotmap in (MapSetoid G H).
  Proof. intros x y Heq. simpl. now rewrite Heq. Qed.

  Lemma Iso1_identical : forall (psi: Homomorph G_N H), 
    f == psi \o quotmap in (MapSetoid G H) ->
    psi == inclusion \o Iso1 in (MapSetoid G_N H).
  Proof.
    intros psi Hiso x y Heq. rewrite Heq.
    rewrite Iso1comp_proper in Hiso.
    rewrite <-Map_assoc in Hiso.
    pose (Map_reduc _ Hiso) as Heq2.
    symmetry. now apply Heq2.
  Qed.
End FundHom.

Section CorrespSubgroup.
  Context {G:Group} {N: NormalSubgroup G} (G_N := CosetGroup N).

  Program Definition ExtendQuotGroups
  : Map (Subgroup G_N) [ K in Subgroup G | N <= K ]
  := map H => GroupableSubsetoid_toSubgroup (Preimage quotmap (Subgroup_toGroupableSetoid H)).
  Next Obligation.
    split. intros H1 H2. simpl. intros [H1H2 H2H1]. split; intros NH;
    now apply (transitivity NH).
  Defined.
  Next Obligation.
    split.
    - intros g h. simpl. intros Hg Hh.
      apply (ferm_op(H := H) Hg Hh).
    - intros g. simpl. intros Hg.
      apply (ferm_inv(H := H) Hg).
    - apply (ferm_id(H := H)).
  Defined.
  Next Obligation.
    split. simpl. intros g Ng.
    assert (g == 1 in G_N) as Hid.
    { simpl. now rewrite invid, ridentical. }
    rewrite Hid. apply (ferm_id(H := H)).
  Defined.
  Next Obligation.
    split. intros A B [AB BA]. split; split; intros x; simpl;
    (apply AB || apply BA).
  Defined.

  Program Definition FoldGroups
    : Map [ K in Subgroup G | N <= K ] (Subgroup G_N)
    := map K => HomImage quothom K.
  Next Obligation.
    split. intros A B. simpl. intros [[AB] [BA]]. split; split;
    intros g Ng.
    - apply AB, H, Ng.
    - apply BA, H, Ng.
  Defined.
  Next Obligation.
    split. intros A B. simpl. intros [AB BA]. split; split; 
    simpl; intros g [h [Ah Eh]]; exists h; split; try apply Eh.
    - apply AB, Ah.
    - apply BA, Ah.
  Defined.

  Lemma corresp_comp_id_sg :
    ExtendQuotGroups \o FoldGroups == Map_id.
  Proof.
    intros [K1 N_K1] [K2 N_K2]. simpl. intros [[K12] [K21]]. split; split;
    intros g; simpl.
    - intros [h [K1h Eh]]. apply K12. apply N_K1 in Eh.
      pose (ferm_op Eh K1h) as K1g.
      now rewrite <-associative, linvertible, ridentical in K1g.
    - intros K2g. exists g; split.
      + apply K21, K2g.
      + rewrite rinvertible. apply ferm_id.
  Defined.

  Lemma corresp_comp_id_qsg :
    FoldGroups \o ExtendQuotGroups == Map_id.
  Proof.
    intros H1 H2. simpl. intros [[H12] [H21]]. split; split;
    intros g. simpl.
    - intros [h [H1h Eh]]. apply H12.
      now rewrite (coset_eq Eh).
    - intros H2g. simpl. exists g. split.
      + now apply H21.
      + rewrite rinvertible. apply ferm_id.
  Defined.
End CorrespSubgroup.


Program Definition DirectProductGroup (G H:Group):=
  grp by binop g, h => (fst g * fst h, snd g * snd h),
            map g => (!(fst g), !(snd g)),
            (1, 1) on [(G, H)].
Next Obligation.
  split. intros g h [Heq0 Heq1] x y [Heq2 Heq3]. split; simpl.
  - now rewrite Heq0, Heq2.
  - now rewrite Heq1, Heq3.
Defined.
Next Obligation.
  split. intros g h [Heq0 Heq1]. split; simpl;
  now (rewrite Heq0 || rewrite Heq1).
Defined.
Next Obligation.
  split; split; simpl; split; try apply associative;
  try apply rinvertible; try apply ridentical.
Defined.

(* Program Definition trivnsg1_prodgrp (G H:Group) :=
  (G, ) *)

Program Definition sg_prod {G:Group} (H1 H2: Subgroup G) :=
  [ g | exists h1 h2, H1 h1 /\ H2 h2 /\ g == h1 * h2 ].
Next Obligation.
  split. intros x y Heq. split; 
  intros [h [n [Hh [Nn Heq1]]]]; exists h, n; split; 
  try split; try apply Hh; try apply Nn;
  now rewrite <-Heq1, Heq.
Defined.
Notation "[  N * H  ]" := (@sg_prod _ N H)
  (at level 0, N, H at next level, no associativity) : alg_scope.

Program Definition sgnsg_prod `(H: Subgroup G) (N: NormalSubgroup G)
  := [ H * N ]  <<- G.
Next Obligation.
  split; simpl.
  - intros x y [hx [nx [Hhx [Nnx Heqx]]]]
    [hy [ny [Hhy [Nny Heqy]]]]. 
    pose (normal(g := !hy) Nnx) as Heq0.
    rewrite invinv in Heq0. 
    exists (hx * hy), (!hy * nx * hy * ny). split; try split.
    + apply (ferm_op Hhx Hhy).
    + apply (ferm_op Heq0 Nny).
    + now rewrite 3!associative, <-(associative hx),
        rinvertible, ridentical, Heqx, Heqy, associative.
  - intros x [h [n [Hh [Nn Heq]]]].
    exists (!h), (h * !n * !h). split; try split.
    + apply ferm_inv, Hh.
    + apply normal, ferm_inv, Nn.
    + now rewrite 2!associative, linvertible, lidentical, 
        Heq, opinv.
  - exists 1, 1. split; try split; try apply ferm_id.
    now rewrite ridentical.
Defined.
Notation "<  H *> N  >" := (@sgnsg_prod _ H N)
  (at level 0, H, N at next level) : alg_scope.

Lemma sg_prod_comm `{H: Subgroup G} {N: NormalSubgroup G} : 
  [ H * N ] == [ N * H ] in SubsetoidSetoid G.
Proof.
  split; split; intros g [h1 [h2 [Hh1 [Hh2 Heq]]]]; simpl.
  - exists (h1 * h2 * !h1), h1; split; try split.
    + now apply normal.
    + trivial.
    + now rewrite <-(associative), linvertible, ridentical.
  - exists h2, (!h2 * h1 * !!h2); split; try split.
    + trivial.
    + now apply normal.
    + now rewrite 2!associative, rinvertible, 
        lidentical, invinv.
Qed.

Lemma stdeq_grpable {G:Group} {A B: Subsetoid G}
  : A == B -> A <- G -> B <- G.
Proof.
  intros AB AG. assert ((GroupableSubsetoid G) A).
  { apply AG. } rewrite AB in H. apply H.
Qed.

Program Definition nsgsg_prod `(N: NormalSubgroup G) (H: Subgroup G)
  := [ N * H ] <<- G.
Next Obligation.
  apply (stdeq_grpable sg_prod_comm), sgnsg_prod_obligation_1.
Defined.
Notation "<  N <* H  >" := (@nsgsg_prod _ N H)
  (at level 0, N, H at next level) : alg_scope.

Program Definition Hom2 `{H: Subgroup G} {N: NormalSubgroup G}
  : Homomorph H (CosetGroup <| N inside < H *> N> |>)
  := hom g => g.
Next Obligation.
  exists g, 1. split; try split.
  - apply H0.
  - apply ferm_id.
  - now rewrite ridentical.
Defined.
Next Obligation.
  split. intros g h. simpl. intros Heq. rewrite Heq, rinvertible.
  apply ferm_id.
Defined.
Next Obligation.
  split. intros g h. simpl. rewrite rinvertible. apply ferm_id.
Defined.

Program Definition Iso2' `{H: Subgroup G} {N: NormalSubgroup G}
  := (@Iso1_kernel _ _ Hom2 <| N inside H |>
      <{ CosetGroup <| N inside <H *> N> |> }> _ _).
Next Obligation.
  split; split; intros [h Hh]; simpl.
  - intros Nh. now rewrite invid, ridentical.
  - intros E. now rewrite invid, ridentical in E.
Defined.
Next Obligation.
  split; split; intros [g [h [n [Hh [Nn Eg]]]]]; simpl.
  - intros _. exists (exist _ h Hh). split. trivial.
    simpl. rewrite Eg. apply normal, Nn.
  - split.
Defined.

Program Definition id_grpsg_iso {G:Group} : Isomorph G <{ G }>
  := iso g => g.
Next Obligation. split. intros g h. simpl. intuition. Defined.
Next Obligation. split. intros g h. simpl. reflexivity. Defined.
Next Obligation. 
  split; split; split; simpl. intuition. intros [y Hy]. now exists y.
Defined.

Program Definition grpidNormalSubgroup_iso {G:Group}
  : Isomorph <{ G }> G := iso g => g.
Next Obligation. split. intros g h. simpl. intuition. Defined.
Next Obligation. split. intros g h. simpl. reflexivity. Defined.
Next Obligation. 
  split; split; split; simpl; intuition. now exists (exist _ y I).
Defined.

Definition Iso2 `{H: Subgroup G} {N: NormalSubgroup G}
  : Isomorph (CosetGroup <| N inside H |>)
    (CosetGroup <| N inside < H *> N > |>)
  := grpidNormalSubgroup_iso iso\o Iso2'.


Program Definition Hom3 {G:Group} {N1 N2: NormalSubgroup G} (Hle: N1 <= N2)
  : Homomorph (CosetGroup N1) (CosetGroup N2)
  :=  hom g in CosetGroup N1 => g.
Next Obligation. split. intros g h. simpl. apply Hle. Defined.
Next Obligation.
  split. intros g h. simpl. rewrite rinvertible. apply ferm_id.
Defined.

Program Definition coset_nsg {G} {N1 N2: NormalSubgroup G} (Hle: N1 <= N2)
  := (sstd by N2 on CosetGroup N1) <<-| (CosetGroup N1).
Next Obligation.
  split. intros g h. simpl. intros Egh. split; intros Ng.
  - apply Hle in Egh. apply ferm_inv in Egh.
    rewrite opinv, invinv in Egh.
    pose (ferm_op Egh Ng) as N2h.
    now rewrite <-associative, linvertible, ridentical in N2h.
  - apply Hle in Egh. pose (ferm_op Egh Ng) as N2g.
    now rewrite <-associative, linvertible, ridentical in N2g.
Defined.
Next Obligation.
  split.
  - intros g h. simpl. apply ferm_op.
  - intros g. simpl. apply ferm_inv.
  - simpl. apply ferm_id.
Defined.
Next Obligation. split. intros g h. simpl. apply normal. Defined.
Notation "<| H /> N |>" := (@coset_nsg _ N H _)
  (at level 0, H, N at next level) : alg_scope.

Program Definition Iso3' {G:Group} {N1 N2: NormalSubgroup G} (Hle: N1 <= N2)
  := (@Iso1_kernel _ _ (Hom3 Hle) (coset_nsg Hle) <{ CosetGroup N2 }> _ _).
Next Obligation.
  split; split; intros g; simpl; intros N2g.
  - now rewrite invid, ridentical.
  - now rewrite invid, ridentical in N2g.
Defined.
Next Obligation.
  split; split; intros g; simpl; intuition. exists g.
  split; trivial. rewrite rinvertible. apply ferm_id.
Defined.

Definition Iso3 {G:Group} {N1 N2: NormalSubgroup G} (Hle: N1 <= N2)
  : Isomorph (CosetGroup <| N2 /> N1 |>) (CosetGroup N2)
  := grpidNormalSubgroup_iso iso\o (Iso3' Hle).

Close Scope alg_scope.
Close Scope setoid_scope.
