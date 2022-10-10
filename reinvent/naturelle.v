
(*===== Base logic =====*)

Inductive Vraie : Prop :=
| identite : Vraie.

Inductive Faux : Prop := .

Inductive et (A B : Prop) : Prop :=
| conjonction : A -> B -> (et A B).

Inductive ou (A B : Prop) : Prop :=
| ougauche : A -> (ou A B)
| oudroite : B -> (ou A B).

Inductive egale (A : Type) (x : A) : A -> Prop :=
| egreflexion : egale A x x.

Definition fegale (A B : Type) (f : A -> B) (x y : A) (H : egale _ x y) :=
  match H in (egale _ _ a) return (egale _ (f x) (f a)) with
  | egreflexion _ _ => egreflexion _ (f x)
  end.

Definition egsym (A : Type) (x y : A) (H : egale _ x y) :=
    match H in (egale _ _ a) return (egale _ a x) with
    | egreflexion _ _ => egreflexion _ x
    end.

Lemma eg_loitransitive: forall (A: Type) (x y z: A),
egale _ x y -> egale _ y z -> egale _ x z.
Proof.
intros A x y z Hxy Hyz.
case Hyz.
apply Hxy.
Qed.

Definition nepas := fun A : Prop => A -> Faux.


(*===== Booleen =====*)

Inductive booleenne : Set :=
| vraie : booleenne
| faux : booleenne.

Definition etb b1 b2 :=
  match b1 with
  | vraie => b2
  | faux => faux
  end.

Definition oub b1 b2 :=
  match b1 with
  | vraie => vraie
  | faux => b2
  end.

Definition nepasb b :=
  match b with
  | vraie => faux
  | faux => vraie
  end.

Definition impliquerb b1 b2 :=
  match b1 with
  | vraie => b2
  | faux => vraie
  end.

Definition xor b1 b2 :=
  match b1 with
  | vraie => nepasb b2
  | faux => b2
  end.
  

(*===== Reflexion =====*)

Definition egbooleenne b1 b2 := nepasb (xor b1 b2).

Definition estvraie b :=
  match b with
  | vraie => Vraie
  | faux => Faux
  end.

Lemma vraieredondant: forall (b: booleenne), egale _ b (egbooleenne b vraie).
Proof.
  induction b; apply egreflexion.
Qed.

Inductive refleter (P : Prop) : booleenne -> Set :=
  | refletervraie : P -> refleter P vraie
  | refleterfaux : (nepas P) -> refleter P faux.

Lemma iffP : forall (P Q : Prop) (b : booleenne),
  refleter P b -> (P -> Q) -> (Q -> P) -> refleter Q b.
Proof.
  intros P Q b HPb HPQ HQP.
  case HPb; intros HP.
  - apply refletervraie. apply HPQ; apply HP.
  - apply refleterfaux. intros HQ. apply HQP in HQ. apply HP in HQ. case HQ.
Qed.

Lemma idP : forall (b : booleenne), refleter (estvraie b) b.
Proof.
  intros b.
  case b.
  - apply refletervraie. apply identite.
  - apply refleterfaux. intros F. case F.
Qed.


Lemma introVraieFaux : forall (P : Prop) (b c : booleenne), refleter P b ->
  (match c with
  | vraie => P
  | faux => nepas P
  end) -> estvraie (egbooleenne b c).
Proof.
  intros P b c Hb.
  case c; case Hb; intros H1 H2.
  - apply identite.
  - apply H1 in H2. case H2.
  - apply H2 in H1. case H1.
  - apply identite.
Qed.

Lemma elimVraieFaux : forall (P : Prop) (b c : booleenne), refleter P b -> estvraie (egbooleenne b c) ->
  (match c with
  | vraie => P
  | faux => nepas P
  end).
Proof.
  intros P b c HPb.
  induction HPb; case c; intros Hbc.
  - apply p.
  - case Hbc.
  - case Hbc.
  - apply n.
Qed.

Lemma elimVraie : forall (P : Prop) (b : booleenne), refleter P b -> estvraie b -> P.
Proof.
  intros P b HPb Hb.
  apply (elimVraieFaux P b vraie HPb).
  case (vraieredondant b).
  apply Hb.
Qed.

Lemma introVraie : forall (P : Prop) (b : booleenne), refleter P b -> P -> estvraie b.
Proof.
  intros P b Hb HP.
  assert (estvraie (egbooleenne b vraie) -> estvraie b).
  {
    case (vraieredondant b).
    intro Hbv; apply Hbv.
  }
  apply (H (introVraieFaux P b vraie Hb HP)).
Qed.


(*===== Direct product =====*)

Inductive produit (A B : Type) : Type :=
| paire : A -> B -> produit A B.

Definition premiere := fun (A B : Type) (p : produit A B)
  => match p with
  | paire _ _ x _ => x
  end.

Definition deuxieme := fun (A B : Type) (p : produit A B)
  => match p with
  | paire _ _ _ x => x
  end.


(*===== Natural number =====*)

Inductive naturelle : Set :=
| nulle : naturelle
| successeur : naturelle -> naturelle.

Fixpoint ajouter (n m : naturelle) {struct n} : naturelle :=
  match n with
  | nulle => m
  | successeur n' => successeur (ajouter n' m)
  end.

Fixpoint soustraire (n m : naturelle) {struct n} : naturelle :=
  match n, m with
  | nulle, _ => nulle
  | _, nulle => n
  | successeur n', successeur m' => soustraire n' m'
  end.

Fixpoint multiplier (n m : naturelle) {struct n} : naturelle :=
  match n with
  | nulle => nulle
  | successeur n' => ajouter m (multiplier n' m)
  end.

Fixpoint _diviser (x y q u : naturelle) {struct x} : produit naturelle naturelle :=
  match x with
  | nulle => paire _ _ q u
  | successeur x' =>
    match u with
    | nulle => _diviser x' y (successeur q) y
    | successeur u' => _diviser x' y q u'
    end
  end.

Definition quotient x y :=
  match y with
  | nulle => nulle
  | successeur y' => premiere _ _ (_diviser x y' nulle y')
  end.

Definition modulo x y :=
  match y with
  | nulle => nulle
  | successeur y' => deuxieme _ _ (_diviser x y' nulle y')
  end.

Definition predecesseur (n : naturelle) :=
  match n with
  | nulle => nulle
  | successeur n' => n'
  end.

Definition egalesucc (n m : naturelle) : egale _ (successeur n) (successeur m) -> egale _ n m
  := fegale _ _ predecesseur (successeur n) (successeur m).

Goal forall (n m : naturelle), egale _ n m -> egale _ nulle (soustraire n m).
Proof.
  induction n.
  induction m.
  - simpl. reflexivity.
  - simpl. intros. apply egreflexion.
  - induction m.
  -- simpl. intros. apply egsym. apply H.
  -- simpl. intros. apply IHn. apply egalesucc. apply H.
Qed.

Lemma addNS : forall n, egale _ n (successeur n) -> Faux.
Proof.
  induction n.
  apply (egale_ind _ nulle (fun n => match n with |nulle => Vraie | _ => Faux end) identite (successeur nulle)).
  intros.
  apply egalesucc in H.
  apply IHn. apply H.
Qed.


Record egtaper :=
  EgTaper {
    sorte: Type;
    egop: sorte -> sorte -> booleenne;
    reflegop: forall x y: sorte, refleter (egale _ x y) (egop x y)
  }.

Lemma egP : forall (T : egtaper) (x y : sorte T), refleter (egale _ x y) (egop _ x y).
Proof.
  intro T.
  apply reflegop.
Qed.

Fixpoint egnaturelle (n m : naturelle) :=
  match n, m with
  | nulle, nulle => vraie
  | nulle, successeur _ => faux
  | successeur _, nulle => faux
  | successeur n', successeur m' => egnaturelle n' m'
  end.

Lemma naturelle_egP : forall (n m : naturelle), refleter (egale _ n m) (egnaturelle n m).
Proof.
  induction n; induction m.
  - simpl. apply refletervraie. apply egreflexion.
  - simpl. apply refleterfaux. intros F. apply (egale_ind _ nulle (fun n => match n with |nulle => Vraie |_ => Faux end) identite (successeur m)). apply F.
  - simpl. apply refleterfaux. intros F. apply (egale_ind _ (successeur n) (fun n => match n with |successeur _ => Vraie |nulle => Faux end) identite nulle). apply F.
  - simpl. apply (iffP (estvraie (egnaturelle n m)) (egale _ (successeur n) (successeur m)) (egnaturelle n m)).
  -- apply idP.
  -- case (IHn m).
  --- intros H _. apply fegale. apply H.
  --- intros _ F. case F.
  -- case (IHn m).
  --- intros. apply identite.
  --- intros F1 F2. apply egalesucc in F2. apply F1 in F2. case F2.
Qed. 

Definition trois := successeur (successeur (successeur nulle)).
Definition neuf := Eval compute in multiplier trois trois.
Definition dix := Eval compute in successeur neuf.

Definition naturelle_egTaper := EgTaper naturelle egnaturelle naturelle_egP.

Lemma egvraie_estvraie : forall b : booleenne, egale _ b vraie -> estvraie b.
Proof. intros b H. apply egsym in H. case H. apply identite. Qed.

Lemma estvraie_egvraie : forall b : booleenne, estvraie b -> egale _ b vraie.
Proof.
  induction b.
  - intros _. apply egreflexion.
  - intros F. case F.
Qed.

Definition neufNdix (H : egale _ neuf dix) :=
  Eval compute in (egale_ind _ (egop naturelle_egTaper neuf dix) (fun b => estvraie (nepasb b))
   identite vraie (estvraie_egvraie _ (introVraie _ _ (egP naturelle_egTaper neuf dix) H))) .


(* ===== Ensemble ===== *)

Definition Ensemble (M: Type) := M -> Prop.
Definition ensemble (M: egtaper) := sorte M -> booleenne.

Lemma axiom_ensemble : forall (M: egtaper) (A: ensemble M), 
  forall (x: sorte M), estvraie (oub (A x) (nepasb (A x))).
Proof.
  intros.
  case (A x); apply identite.
Qed.

Axiom Axiom_Ensemble : forall (T: Type) (A: Ensemble T),
  forall (x: T), ou (A x) (nepas (A x)).

Definition VideEnsemble (T: Type): Ensemble T := fun _ => Faux.
Definition MemeEnsemble (T: Type): Ensemble T := fun _ => Vraie.
Definition SousEnsemble (T: Type) (A B: Ensemble T)
  := forall (x: T), A x -> B x.

Definition appartenir (M: egtaper) (x: sorte M) (ens: ensemble M) := estvraie (ens x).

Definition videensemble (M: egtaper): ensemble M := fun _ => faux.
Definition memeensemble (M: egtaper): ensemble M := fun _ => vraie.

Definition sousensemble (M: egtaper) (A B: ensemble M)
  := forall (x: sorte M), appartenir _ x A -> appartenir _ x B.

(* ===== Group ===== *)

Record groupe: Type := _groupe {
  porteur: egtaper;
  support: ensemble porteur;
  operatrice: sorte porteur -> sorte porteur -> sorte porteur;
  inverse: sorte porteur -> sorte porteur;
  elemid: sorte porteur;
  fermer_ope: forall (x y: sorte porteur), 
    appartenir _ x support -> appartenir _ y support
    -> appartenir _ (operatrice x y) support;
  fermer_inv: forall (x: sorte porteur),
    appartenir _ x support -> appartenir _ (inverse x) support;
  fermer_id: appartenir _ elemid support;
  assoc_ope: forall (x y z: sorte porteur),
    appartenir _ x support -> appartenir _ y support -> appartenir _ z support
    -> egale _ (operatrice (operatrice x y) z) (operatrice x (operatrice y z));
  inv_gauche: forall (x: sorte porteur),
    appartenir _ x support -> egale _ elemid (operatrice (inverse x) x);
  inv_droite: forall (x: sorte porteur),
    appartenir _ x support -> egale _ elemid (operatrice x (inverse x));
  id_droite: forall (x: sorte porteur),
    appartenir _ x support -> egale _ x (operatrice x elemid)
}.

Definition gtaper G := sorte (porteur G).
Definition gegop G := egop (porteur G).

Lemma id_gauche: forall (G: groupe) (x: gtaper G),
  appartenir _ x (support G) -> egale _ x (operatrice G (elemid G) x).
Proof.
  intros G x H.
  case (egsym _ _ _ (inv_droite G x H)).
  case (egsym _ _ _ (assoc_ope _ x (inverse _ x) x H (fermer_inv _ x H) H)).
  case (inv_gauche G x H).
  case (id_droite G x H).
  apply egreflexion.
Qed.

Definition homomorphisme (G H: groupe) (f: gtaper H -> gtaper G) :=
  (forall x: gtaper H, appartenir _ x (support H) -> appartenir _ (f x) (support G)) ->
  egale _ (f (elemid H)) (elemid G) ->
  (forall x y: gtaper H, egale _ (f (operatrice H x y)) (operatrice G (f x) (f y))) ->
  (forall x: gtaper H, egale _ (f (inverse H x)) (inverse G (f x))).


Definition noyau (G H: groupe) (f: gtaper H -> gtaper G) : ensemble (porteur H) :=
  fun x => gegop _ (elemid G) (f x).

(* Definition image (G H: groupe) (f: gtaper H -> gtaper G) : ensemble (porteur G) := *)


Record Groupe: Type := _Groupe {
  Porteur: Type;
  Support: Ensemble Porteur;
  Operatrice: Porteur -> Porteur -> Porteur;
  Inverse: Porteur -> Porteur;
  Elemid: Porteur;
  Fermer_ope: forall (x y: Porteur), 
    Support x -> Support y -> Support (Operatrice x y);
  Fermer_inv: forall (x: Porteur),
    Support x -> Support (Inverse x);
  Fermer_id: Support Elemid;
  Assoc_ope: forall (x y z: Porteur),
    Support x -> Support y -> Support z
    -> egale _ (Operatrice (Operatrice x y) z) (Operatrice x (Operatrice y z));
  Inv_gauche: forall (x: Porteur),
    Support x -> egale _ Elemid (Operatrice (Inverse x) x);
  Inv_droite: forall (x: Porteur),
    Support x -> egale _ Elemid (Operatrice x (Inverse x));
  Id_droite: forall (x: Porteur),
    Support x -> egale _ x (Operatrice x Elemid)
}.

Lemma Id_gauche: forall (G: Groupe) (x: Porteur G),
  (Support G) x -> egale _ x (Operatrice _ (Elemid G) x).
Proof.
  intros G x H.
  case (egsym _ _ _ (Inv_droite G x H)).
  case (egsym _ _ _ (Assoc_ope _ x (Inverse _ x) x H (Fermer_inv _ x H) H)).
  case (Inv_gauche G x H).
  case (Id_droite G x H).
  apply egreflexion.
Qed.

Lemma Reduire_gauche: forall (G: Groupe) (x y z: Porteur G), 
  (Support G) x -> (Support G) y -> (Support G) z
  -> egale _ (Operatrice _ x y) (Operatrice _ x z)
  -> egale _ y z.
Proof.
  intros G x y z Gx Gy Gz Hxyxz.
  case (egsym _ _ _(Id_gauche _ y Gy)).
  case (egsym _ _ _(Id_gauche _ z Gz)).
  case (egsym _ _ _ (Inv_gauche _ x Gx)).
  case (egsym _ _ _ (Assoc_ope _ (Inverse _ x) x y (Fermer_inv _ x Gx) Gx Gy)).
  case (egsym _ _ _ (Assoc_ope _ (Inverse _ x) x z (Fermer_inv _ x Gx) Gx Gz)).
  apply fegale, Hxyxz.
Qed.

Lemma Transpo_gauche: forall (G: Groupe) (x y z: Porteur G),
  (Support G) x -> (Support G) y -> (Support G) z
  -> egale _ (Operatrice _ x y) z -> egale _ y (Operatrice _ (Inverse _ x) z).
Proof.
  intros G x y z Gx Gy Gz H0.
  case (egsym _ _ _ (Id_gauche _ y Gy)).
  case (egsym _ _ _ (Inv_gauche _ x Gx)).
  case (egsym _ _ _ (Assoc_ope _ (Inverse _ x) x y (Fermer_inv _ x Gx) Gx Gy)).
  apply fegale, H0.
Qed.

Lemma InvInv: forall (G: Groupe) (x: Porteur G),
  (Support G) x -> egale _ x (Inverse _ (Inverse _ x)).
Proof.
  intros G x Gx.
  pose (Fermer_inv _ x Gx) as Ginvx.
  apply (Reduire_gauche _ (Inverse _ x) x (Inverse _ (Inverse _ x)) Ginvx Gx (Fermer_inv _ (Inverse _ x) Ginvx)).
  case (Inv_gauche _ x Gx).
  case (Inv_droite _ (Inverse _ x) Ginvx).
  apply egreflexion.
Qed.


Definition cartographie (T1 T2: Type) (A: Ensemble T1) (B: Ensemble T2)
  (f: T1 -> T2) := forall (x: T1), A x -> B (f x).

Definition injection (T1 T2: Type) (A: Ensemble T1) (B: Ensemble T2)
  (f: T1 -> T2)
  := (cartographie _ _ A B f) -> forall x y: T1, A x -> A y -> egale _ (f x) (f y) -> egale _ x y.

Definition Homomorphisme (G H: Groupe) (f: Porteur H -> Porteur G) 
  := et (cartographie _ _ (Support H) (Support G) f)
   (forall x y: Porteur H, egale _ (f (Operatrice H x y)) (Operatrice G (f x) (f y))).

Theorem Hom_preserve_id: forall (G H: Groupe) (f: Porteur H -> Porteur G),
  Homomorphisme _ _ f -> egale _ (Elemid G) (f (Elemid H)).
Proof.
  intros G H f _Hhom.
  unfold Homomorphisme in _Hhom.
  case _Hhom.
  intros Hcart Hhom.
  unfold cartographie in Hcart.
  case (egsym _ _ _ (Inv_gauche _ (f (Elemid H)) (Hcart (Elemid H) (Fermer_id H)))).
  apply egsym.
  pose (Hcart (Elemid H) (Fermer_id H)) as Gfe.
  apply (Transpo_gauche _ (f (Elemid H)) (f (Elemid H)) (f (Elemid H)) Gfe Gfe Gfe).
  case (Hhom (Elemid H) (Elemid H)).
  case (Id_droite _ (Elemid H) (Fermer_id H)).
  apply egreflexion.
Qed.

Theorem Hom_preserve_inv: forall (G H: Groupe) (f: Porteur H -> Porteur G),
  Homomorphisme _ _ f -> 
  forall (x: Porteur H), (Support H) x -> egale _ (f (Inverse _ x)) (Inverse _ (f x)).
Proof.
  intros G H f _Hhom.
  case _Hhom.
  intros Hcart Hhom.
  intros x Hx.
  unfold cartographie in Hcart.
  pose (Fermer_inv _ (f x) (Hcart x Hx)) as Ginvfx.
  case (egsym _ _ _ (Id_droite _ (Inverse _ (f x)) Ginvfx)).
  apply (Transpo_gauche _ _ _ _ (Hcart x Hx) (Hcart (Inverse _ x) (Fermer_inv _ x Hx)) (Fermer_id _)).
  case Hhom.
  case (Inv_droite _ _ Hx).
  apply (egsym _ _ _ (Hom_preserve_id _ _ f _Hhom)).
Qed.

Definition SousGroupe (G: Groupe) (Hsupp: Ensemble (Porteur G))
  (HsousG: SousEnsemble _ Hsupp (Support G))
  (HFermer_ope: forall (x y: Porteur G), Hsupp x -> Hsupp y -> Hsupp (Operatrice G x y))
  (HFermer_inv: forall (x: Porteur G), Hsupp x -> Hsupp (Inverse G x))
  (HFermer_id: Hsupp (Elemid G))
  
  := _Groupe (Porteur G) Hsupp (Operatrice G) (Inverse G) (Elemid G)
  HFermer_ope HFermer_inv HFermer_id
  (fun (x y z: Porteur G) (Hx: Hsupp x) (Hy: Hsupp y) (Hz: Hsupp z)
   => Assoc_ope G x y z (HsousG x Hx) (HsousG y Hy) (HsousG z Hz))
  (fun (x: Porteur G) (Hx: Hsupp x) => Inv_gauche G x (HsousG x Hx))
  (fun (x: Porteur G) (Hx: Hsupp x) => Inv_droite G x (HsousG x Hx))
  (fun (x: Porteur G) (Hx: Hsupp x) => Id_droite G x (HsousG x Hx)).



Definition SousGroupeNormal (G H: Groupe) (f: Porteur H -> Porteur G) (Homomorphisme G H f)

Definition Noyau_Supp (G H: Groupe) (f: Porteur H -> Porteur G) : Ensemble (Porteur H) :=
  fun x => egale _ (Elemid G) (f x).