
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

Axiom fonc_egalite: forall (A: Type) (B: A -> Type) (f g: forall x:A, B x),
  (forall x: A, egale _ (f x) (g x)) -> egale _ f g.

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

Definition ssi (A B: Prop) := et (A -> B) (B -> A).


(*===== Booleen =====*)

Inductive booleenne : Set :=
| vraie : booleenne
| faux : booleenne.

Definition nepasb b :=
  match b with
  | vraie => faux
  | faux => vraie
  end.

Definition egb b1 b2 :=
  match b1 with
  | vraie => b2
  | faux => nepasb b2
  end.

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

Definition impliqb b1 b2 :=
  match b1 with
  | vraie => b2
  | faux => vraie
  end.

Definition xor b1 b2 := nepasb (egb b1 b2).

Definition estvraie b :=
  match b with
  | vraie => Vraie
  | faux => Faux
  end.
  

(*===== Reflexion =====*)



Inductive refleter (P : Prop): booleenne -> Set :=
  | refletervraie : P -> refleter P vraie
  | refleterfaux : (nepas P) -> refleter P faux.

Lemma iffP : forall (P Q : Prop) (b : booleenne),
  refleter P b -> (ssi P Q) -> refleter Q b.
Proof.
  intros P Q b HPb HPQ.
  case HPQ as [HPQ HQP].
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

Lemma egb_egale: forall (b1 b2: booleenne), refleter (egale _ b1 b2) (egb b1 b2).
Proof.
  intros b1 b2.
  case b1, b2.
  - apply refletervraie, egreflexion.
  - apply refleterfaux. unfold nepas. apply (egale_ind _ vraie (estvraie) identite faux).
  - apply refleterfaux. unfold nepas. apply (egale_ind _ faux (fun b => estvraie (nepasb b)) identite vraie).
  - apply refletervraie, egreflexion.
Qed.

Lemma vraie_redondant: forall (b: booleenne), ssi (estvraie b) (estvraie (egb vraie b)).
Proof.
  intros b.
  apply conjonction; case b.
  - intros _; apply identite.
  - intros F; case F.
  - intros _; apply identite.
  - intros F; case F.
Qed.

Lemma introVraieFaux : forall (P : Prop) (c b : booleenne), refleter P b ->
  (match c with
  | vraie => P
  | faux => nepas P
  end) -> estvraie (egb c b).
Proof.
  intros P c b Hb.
  case c; case Hb; intros H1 H2.
  - apply identite.
  - apply H1 in H2. case H2.
  - apply H2 in H1. case H1.
  - apply identite.
Qed.

Lemma elimVraieFaux : forall (P : Prop) (c b : booleenne), refleter P b -> estvraie (egb c b) ->
  (match c with
  | vraie => P
  | faux => nepas P
  end).
Proof.
  intros P c b HPb.
  induction HPb; case c; intros Hbc.
  - apply p.
  - case Hbc.
  - case Hbc.
  - apply n.
Qed.

Lemma elimVraie : forall (P : Prop) (b : booleenne), refleter P b -> estvraie b -> P.
Proof.
  intros P b HPb Hb.
  case (vraie_redondant b); intros Hb' _; apply Hb' in Hb.
  apply (elimVraieFaux P vraie b HPb Hb).
Qed.

Lemma introVraie : forall (P : Prop) (b : booleenne), refleter P b -> P -> estvraie b.
Proof.
  intros P b HPb HP.
  case (vraie_redondant b); intros _ Hb; apply Hb.
  apply (introVraieFaux P vraie b HPb HP).
Qed.

Lemma impliqP: forall b1 b2, refleter (estvraie b1 -> estvraie b2) (impliqb b1 b2).
Proof.
  intros b1 b2; case b1, b2.
  - apply refletervraie. intros. apply identite.
  - apply refleterfaux. intros F. apply F, identite.
  - apply refletervraie. intros F; case F.
  - apply refletervraie. intros F; apply F.
Qed.

Section ProduitDirect.

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
End ProduitDirect.

Section Naturelle.

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
  - apply refletervraie, egreflexion.
  - apply refleterfaux; unfold nepas. apply (egale_ind _ nulle (fun n => match n with |nulle => Vraie |_ => Faux end) identite (successeur m)).
  - apply refleterfaux; unfold nepas. apply (egale_ind _ (successeur n) (fun n => match n with |successeur _ => Vraie |nulle => Faux end) identite nulle).
  - apply (iffP (estvraie (egnaturelle n m)) (egale _ (successeur n) (successeur m)) (egnaturelle n m)).
  -- apply idP.
  -- apply conjonction.
  --- case (IHn m).
  ---- intros H _. apply fegale. apply H.
  ---- intros _ F. case F.
  --- case (IHn m).
  ---- intros. apply identite.
  ---- intros F1 F2. apply egalesucc in F2. apply F1 in F2. case F2.
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

End Naturelle.



Module Ensemble.
  Section ClasseDef.

    Record classe_de (T: Type) := Classe {
      avoir: T -> Prop;
      eg: T -> T -> Prop;
      exclu: forall (x: T), ou (avoir x) (nepas (avoir x))
    }.

    Structure taper := Paquet { sorte; classe: classe_de sorte }.
    (* Definition classe (cT: taper) := classe_de (sorte cT). *)
  End ClasseDef.

  Module Exports.
    (* Coercion porteur: taper >-> Sortclass. *)
    Notation ensembleTaper := taper.
    Definition avoir T := avoir _ (classe T).
    Definition eg T := eg _ (classe T).
    Definition exclu T := exclu _ (classe T).
  End Exports.
End Ensemble.
Import Ensemble.Exports.

Section EnsembleTheorie.
  Variable T: Type.
  Definition inc (A B: Type) (H: egale _ A B): A -> B :=
    match H in (egale _ _ T) return (_ -> T) with
    | egreflexion _ _ => (fun x => x)
    end.
  Eval compute in (inc _ _ (egreflexion _ _) nulle).

  Definition f_vide := (fun _: T => Faux).
  Lemma f_vide_exclu: forall (x: T), ou (f_vide x) (nepas (f_vide x)).
  Proof. intros x; apply oudroite; intros F; case F. Qed.
  Definition VideEnsemble :=
    Ensemble.Classe T f_vide (egale T) f_vide_exclu.

  Definition f_meme := (fun _: T => Vraie).
  Lemma f_meme_exclu: forall (x: T), ou (f_meme x) (nepas (f_meme x)).
  Proof. intros x; apply ougauche; apply identite. Qed.
  Definition MemeEnsemble := 
    Ensemble.Classe T f_meme (egale T) f_meme_exclu.

End EnsembleTheorie.

Section CartographieTheorie.
  Variables A B: ensembleTaper.
  Definition Ta := Ensemble.sorte A.
  Definition Tb := Ensemble.sorte B.

  Definition fermer (f: Ta -> Tb) := forall x, avoir A x -> avoir B (f x).
  Definition sousensemble (H: egale _ Ta Tb) := fermer (inc _ _ H).
End CartographieTheorie.

Module Cartographie.
  Section ClasseDef.

    Record classe_de := Classe {
      domaine: ensembleTaper;
      codomaine: ensembleTaper;
      carto: Ensemble.sorte domaine -> Ensemble.sorte codomaine;
      fermer: fermer _ _ carto
    }.

  End ClasseDef.

  Module Exports.
    Notation cartoTaper := classe_de.
  End Exports.
End Cartographie.
Import Cartographie.Exports.

Fixpoint nompaire n :=
  match n with
  | nulle => vraie
  | successeur n' => nepasb (nompaire n')
  end.

Fixpoint multde4 n :=
  match n with
  | nulle => vraie
  | successeur nulle => faux
  | successeur (successeur nulle) => faux
  | successeur (successeur (successeur nulle)) => faux
  | successeur (successeur (successeur (successeur n'))) => multde4 n'
  end.

Lemma nepasb_nepasb: forall (b: booleenne),
  estvraie (egb b (nepasb (nepasb b))).
Proof. intros b; case b; apply identite. Qed.

Lemma multde4_nompaire: forall (n: naturelle),
  estvraie (impliqb (multde4 n) (nompaire n)).
Proof.
  fix multde4_nompaire 1.
  intros n; destruct n as [|[|[|[|n]]]]; try apply identite.
  simpl. 
  case (elimVraie _ _ (egb_egale (nompaire n) (nepasb (nepasb (nompaire n)))) (nepasb_nepasb (nompaire n))).
  case (elimVraie _ _ (egb_egale (nompaire n) (nepasb (nepasb (nompaire n)))) (nepasb_nepasb (nompaire n))).
  apply multde4_nompaire.
Qed.


Definition nomimpaire := fun n => nepasb (nompaire n).

Lemma bool_exclu: forall (b: booleenne), ou (estvraie b) (nepas (estvraie b)).
Proof.
  intros b; case b.
  - apply ougauche, identite.
  - apply oudroite; intros F; case F.
Qed.

Definition nompaireensemble := Ensemble.Paquet _ (
  Ensemble.Classe naturelle (fun n => estvraie (nompaire n)) (egale naturelle) (fun n => bool_exclu (nompaire n))).

Definition multde4ensemble := Ensemble.Paquet _ (
  Ensemble.Classe naturelle (fun n => estvraie (multde4 n)) (egale naturelle) (fun n => bool_exclu (multde4 n))).



Lemma sous_multde4_nompaire: sousensemble multde4ensemble nompaireensemble (egreflexion _ _).
Proof.
  unfold sousensemble, Ta. simpl.
  unfold fermer. intros n.
  apply (elimVraie _ _ (impliqP _ _)).
  apply multde4_nompaire.
Qed.

Record SousEnsMelange (A: Ensemble) := _SousEnsMelange {

}
  := forall (x: T), A x -> B x.

Definition appartenir (M: egtaper) (x: sorte M) (ens: ensemble M) := estvraie (ens x).

Definition videensemble (M: egtaper): ensemble M := fun _ => faux.
Definition memeensemble (M: egtaper): ensemble M := fun _ => vraie.

Definition sousensemble (M: egtaper) (A B: ensemble M)
  := forall (x: sorte M), appartenir _ x A -> appartenir _ x B.
  
Record Cartographie := _Cartographie {
  Tdom: Type;
  Tcod: Type;
  Domaine: Ensemble Tdom;
  Codomaine: Ensemble Tcod;
  Fonc: Tdom -> Tcod;
  Fermer_fonc : forall (x: Tdom), Domaine x -> Codomaine (Fonc x)
}.

Definition Injection (f: Cartographie)
  := forall (x y: Tdom f), Domaine _ x -> Domaine _ y -> egale _ (Fonc f x) (Fonc f y) -> egale _ x y.

Definition Surjection (f: Cartographie)
  := forall (x: Tcod f), exists x': Tdom f, egale _ x (Fonc f x').

Definition Bijection (f: Cartographie) := et (Injection f) (Surjection f).

(* ===== Group ===== *)
(* 
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
  fun x => gegop _ (elemid G) (f x). *)

(* Definition image (G H: groupe) (f: gtaper H -> gtaper G) : ensemble (porteur G) := *)


Record Groupe: Type := _Groupe {
  Tsupp: Type;
  Supp: Ensemble Tsupp;
  Ope: Tsupp -> Tsupp -> Tsupp;
  Inv: Tsupp -> Tsupp;
  Id: Tsupp;
  Fermer_ope: forall (x y: Tsupp), 
    Supp x -> Supp y -> Supp (Ope x y);
  Fermer_inv: forall (x: Tsupp),
    Supp x -> Supp (Inv x);
  Fermer_id: Supp Id;
  Assoc_ope: forall (x y z: Tsupp),
    Supp x -> Supp y -> Supp z
    -> egale _ (Ope x (Ope y z)) (Ope (Ope x y) z);
  Inv_gauche: forall (x: Tsupp),
    Supp x -> egale _ Id (Ope (Inv x) x);
  Inv_droite: forall (x: Tsupp),
    Supp x -> egale _ Id (Ope x (Inv x));
  Id_droite: forall (x: Tsupp),
    Supp x -> egale _ x (Ope x Id)
}.

Lemma Id_gauche: forall (G: Groupe) (x: Tsupp G),
  (Supp G) x -> egale _ x (Ope _ (Id G) x).
Proof.
  intros G x H.
  case (egsym _ _ _ (Inv_droite G x H)).
  case (Assoc_ope _ x (Inv _ x) x H (Fermer_inv _ x H) H).
  case (Inv_gauche G x H).
  case (Id_droite G x H).
  apply egreflexion.
Qed.

Lemma Reduire_gauche: forall (G: Groupe) (x y z: Tsupp G), 
  (Supp G) x -> (Supp G) y -> (Supp G) z
  -> egale _ (Ope _ x y) (Ope _ x z)
  -> egale _ y z.
Proof.
  intros G x y z Gx Gy Gz Hxyxz.
  case (egsym _ _ _(Id_gauche _ y Gy)).
  case (egsym _ _ _(Id_gauche _ z Gz)).
  case (egsym _ _ _ (Inv_gauche _ x Gx)).
  case (Assoc_ope _ (Inv _ x) x y (Fermer_inv _ x Gx) Gx Gy).
  case (Assoc_ope _ (Inv _ x) x z (Fermer_inv _ x Gx) Gx Gz).
  apply fegale, Hxyxz.
Qed.

Lemma Transpo_gauche: forall (G: Groupe) (x y z: Tsupp G),
  (Supp G) x -> (Supp G) y -> (Supp G) z
  -> egale _ (Ope _ y x) z -> egale _ x (Ope _ (Inv _ y) z).
Proof.
  intros G y x z Gy Gx Gz H0.
  case (egsym _ _ _ (Id_gauche _ y Gy)).
  case (egsym _ _ _ (Inv_gauche _ x Gx)).
  case (Assoc_ope _ (Inv _ x) x y (Fermer_inv _ x Gx) Gx Gy).
  apply fegale, H0.
Qed.

Lemma Invdinv_ident: forall (G: Groupe) (x: Tsupp G),
  (Supp G) x -> egale _ x (Inv _ (Inv _ x)).
Proof.
  intros G x Gx.
  pose (Fermer_inv _ x Gx) as Ginvx.
  case (Reduire_gauche _ (Inv _ x) x (Inv _ (Inv _ x)) Ginvx Gx (Fermer_inv _ (Inv _ x) Ginvx)).
  case (Inv_gauche _ x Gx).
  case (Inv_droite _ (Inv _ x) Ginvx).
  apply egreflexion.
  apply egreflexion.
Qed.

Lemma Invope_opeinvinv: forall (G: Groupe) (x y: Tsupp G),
  (Supp G) x -> (Supp G) y -> egale _ (Inv _ (Ope _ x y)) (Ope _ (Inv _ y) (Inv _ x)).
Proof.
  intros G x y Gx Gy.
  pose (Fermer_inv _ _ (Fermer_ope _ _ _ Gx Gy)) as Ginvxy.
  apply (Transpo_gauche _ _ _ _ Ginvxy Gy (Fermer_inv _ _ Gx)).
  case (egsym _ _ _(Id_droite _ _ (Fermer_inv _ _ Gx))).
  apply (Transpo_gauche _ _ _ _ (Fermer_ope _ _ _ Gy Ginvxy) Gx (Fermer_id _)).
  case (egsym _ _ _ (Assoc_ope _ _ _ _ Gx Gy Ginvxy)).
  case (Inv_droite _ _ (Fermer_ope _ _ _ Gx Gy)).
  apply egreflexion.
Qed.

Lemma Id_invid: forall (G: Groupe), egale _ (Id G) (Inv _ (Id _)).
Proof.
  intros G.
  case (egsym _ _ _ (Id_droite G _ (Fermer_inv _ _ (Fermer_id _)))).
  apply (Transpo_gauche _ _ _ _ (Fermer_id _) (Fermer_id _) (Fermer_id _)).
  case (Id_droite _ _ (Fermer_id G)).
  apply egreflexion.
Qed.


Definition Homomorphisme (G H: Groupe) 
  := forall x y: Tsupp H, Supp H x -> Supp H y -> egale _ (f (Ope H x y)) (Ope G (f x) (f y))).

Theorem Hom_preserve_id: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  Homomorphisme _ _ f -> egale _ (Id G) (f (Id H)).
Proof.
  intros G H f _Hhom.
  unfold Homomorphisme in _Hhom.
  case _Hhom.
  intros Hcart Hhom.
  unfold cartographie in Hcart.
  case (egsym _ _ _ (Inv_gauche _ (f (Id H)) (Hcart (Id H) (Fermer_id H)))).
  apply egsym.
  pose (Hcart (Id H) (Fermer_id H)) as Gfe.
  apply (Transpo_gauche _ (f (Id H)) (f (Id H)) (f (Id H)) Gfe Gfe Gfe).
  case (Hhom (Id H) (Id H) (Fermer_id _) (Fermer_id _)).
  case (Id_droite _ (Id H) (Fermer_id H)).
  apply egreflexion.
Qed.

Theorem Hom_preserve_inv: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  Homomorphisme _ _ f -> 
  forall (x: Tsupp H), (Supp H) x -> egale _ (f (Inv _ x)) (Inv _ (f x)).
Proof.
  intros G H f _Hhom.
  case _Hhom.
  intros Hcart Hhom.
  intros x Hx.
  unfold cartographie in Hcart.
  pose (Fermer_inv _ (f x) (Hcart x Hx)) as Ginvfx.
  case (egsym _ _ _ (Id_droite _ (Inv _ (f x)) Ginvfx)).
  apply (Transpo_gauche _ _ _ _ (Hcart x Hx) (Hcart (Inv _ x) (Fermer_inv _ x Hx)) (Fermer_id _)).
  case (Hhom _ _ Hx (Fermer_inv _ _ Hx)).
  case (Inv_droite _ _ Hx).
  apply (egsym _ _ _ (Hom_preserve_id _ _ f _Hhom)).
Qed.

Record SousGroupeMelange (G: Groupe): Type := _SousGroupeMelange {
  Hsupp: Ensemble (Tsupp G);
  HsousG : SousEnsemble _ Hsupp (Supp G);
  HFermer_ope: forall (x y: Tsupp G), Hsupp x -> Hsupp y -> Hsupp (Ope G x y);
  HFermer_inv: forall (x: Tsupp G), Hsupp x -> Hsupp (Inv G x);
  HFermer_id: Hsupp (Id G)
}.

Definition SousGroupe (G: Groupe) (H: SousGroupeMelange G)
  := _Groupe (Tsupp G) (Hsupp G H) (Ope G) (Inv G) (Id G)
  (HFermer_ope _ _) (HFermer_inv _ _) (HFermer_id _ _)
  (fun (x y z: Tsupp G) (Hx: (Hsupp _ _) x) (Hy: (Hsupp _ _) y) (Hz: (Hsupp _ _) z)
   => Assoc_ope G x y z ((HsousG _ _) x Hx) ((HsousG _ _) y Hy) ((HsousG _ _) z Hz))
  (fun (x: Tsupp G) (Hx: (Hsupp _ _) x) => Inv_gauche G x ((HsousG _ _) x Hx))
  (fun (x: Tsupp G) (Hx: (Hsupp _ _) x) => Inv_droite G x ((HsousG _ _) x Hx))
  (fun (x: Tsupp G) (Hx: (Hsupp _ _) x) => Id_droite G x ((HsousG _ _) x Hx)).

Record reldequiv := _reldequiv {
  relsorte: Type;
  relens: Ensemble relsorte;
  rel: relsorte -> relsorte -> Prop;
  loireflexe: forall a: relsorte, relens a -> rel a a;
  loisymetrie: forall a b: relsorte, relens a -> relens b -> rel a b -> rel b a;
  loitransitive: forall a b c: relsorte, relens a -> relens b -> relens c -> rel a b -> rel b c -> rel a c
}.

(* relens の内部について同値関係がwell-definedなら外部がどうなろうと知ったこっちゃないので
   (rel R) y -> みたいなチェックは省く。そもそも実用上relにチェックが内包されそうだけどね。 *)
Inductive classdequivs (R: reldequiv): Type :=
| classdequiv : relsorte R -> classdequivs R.

Definition classdequivCommeEnsemble (R: reldequiv) (Cx: classdequivs R): Ensemble (relsorte _) :=
  match Cx with
  | classdequiv _ x => rel R x
  end.

Axiom classdequiv_egalite: forall (R: reldequiv) (Cx Cy: classdequivs R),
  (forall a, (relens _ a) -> ssi ((classdequivCommeEnsemble _ Cx) a) ((classdequivCommeEnsemble _ Cy) a)) -> egale _ Cx Cy.

Lemma egale_classdequivs: forall (R: reldequiv) (x y: relsorte R),
  relens _ x -> relens _ y -> rel _ x y -> egale _ (classdequiv _ x) (classdequiv _ y).
Proof.
  intros R x y Rx Ry Rxy.
  apply classdequiv_egalite.
  simpl.
  unfold ssi.
  intros a Ra.
  apply conjonction.
  - intros Rxa. apply (loisymetrie _ _ _ Rx Ry) in Rxy. apply (loitransitive _ _ _ _ Ry Rx Ra Rxy Rxa).
  - intros Rya. apply (loitransitive _ _ _ _ Rx Ry Ra Rxy Rya).
Qed.

Definition EnsembleDeQuotient (R: reldequiv) : Ensemble (classdequivs R) :=
  fun Cx => forall x: relsorte R, (classdequivCommeEnsemble _ Cx) x -> relens _ x.

Definition CosetGaucheRel (G: Groupe) (Hmel: SousGroupeMelange G) :=
  fun x y => (Hsupp _ Hmel) (Ope G (Inv G x) y).

Lemma CosetGauche_reflexe (G: Groupe) (Hmel: SousGroupeMelange G):
  forall x: Tsupp G, (Supp G) x -> CosetGaucheRel _ Hmel x x.
Proof.
  intros x Gx.
  unfold CosetGaucheRel.
  case (Inv_gauche _ _ Gx).
  apply HFermer_id.
Qed.

Lemma CosetGauche_symetrie (G: Groupe) (Hmel: SousGroupeMelange G):
  forall x y: Tsupp G, (Supp G) x -> (Supp G) y -> CosetGaucheRel _ Hmel x y -> CosetGaucheRel _ Hmel y x.
Proof.
  unfold CosetGaucheRel.
  intros x y Gx Gy Hxinvy.
  case (egsym _ _ _ (InvInv _ _ Gx)).
  case (OpeInv _ _ _ (Fermer_inv _ _ Gx) Gy).
  apply HFermer_inv.
  apply Hxinvy.
Qed.

Lemma CosetGauche_transitive (G: Groupe) (Hmel: SousGroupeMelange G):
  forall x y z: Tsupp G, (Supp G) x -> (Supp G) y -> (Supp G) z ->
  CosetGaucheRel _ Hmel x y -> CosetGaucheRel _ Hmel y z -> CosetGaucheRel _ Hmel x z.
Proof.
  unfold CosetGaucheRel.
  intros x y z Gx Gy Gz Hxinvy Hyinvz.
  case (egsym _ _ _ (Id_gauche _ _ Gz)).
  case (egsym _ _ _ (Inv_droite _ _ Gy)).
  case (egsym _ _ _ (Assoc_ope _ _ _ _ Gy (Fermer_inv _ _ Gy) Gz)).
  case (Assoc_ope _ _ _ _ (Fermer_inv _ _ Gx) Gy (Fermer_ope _ _ _ (Fermer_inv _ _ Gy) Gz)).
  apply (HFermer_ope _ _ _ _ Hxinvy Hyinvz).
Qed.

Definition CosetGaucheRel_est_reldequiv (G: Groupe) (Hmel: SousGroupeMelange G) :=
  _reldequiv (Tsupp G) (Supp G) (CosetGaucheRel G Hmel)
  (CosetGauche_reflexe _ _) (CosetGauche_symetrie _ _) (CosetGauche_transitive _ _).


Definition SousGroupeNormal (G: Groupe) (Hmel: SousGroupeMelange G) :=
  forall g h: Tsupp G, Supp _ g -> Hsupp _ Hmel h -> Hsupp _ Hmel (Ope _ (Ope _ g h) (Inv _ g)).



Definition Noyau (G H: Groupe) (f: Tsupp H -> Tsupp G) : Ensemble (Tsupp H) :=
  fun x => et (Supp H x) (egale _ (Id G) (f x)).

Lemma SousNoyau: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  SousEnsemble _ (Noyau _ _ f) (Supp H).
Proof.
  unfold Noyau, SousEnsemble.
  intros G H f x Hnoy.
  case Hnoy. intros Hx _.
  apply Hx.
Qed.

Lemma NoyauFermer_ope: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  Homomorphisme _ _ f -> forall x y, Noyau _ _ f x -> Noyau _ _ f y -> Noyau _ _ f (Ope _ x y).
Proof.
  unfold Noyau.
  unfold Homomorphisme.
  intros G H f _Hhom x y Nx Ny.
  case _Hhom. intros Hcart Hhom.
  case Nx as [Hx efx], Ny as [Hy efy].
  case (egsym _ _ _ (Hhom x y Hx Hy)).
  case efx, efy.
  case (Id_droite _ _ (Fermer_id _)).
  apply conjonction.
  apply (Fermer_ope _ _ _ Hx Hy).
  apply egreflexion.
Qed.

Lemma NoyauFermer_inv: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  Homomorphisme _ _ f -> forall x, Noyau _ _ f x -> Noyau _ _ f (Inv _ x).
Proof.
  unfold Noyau.
  intros G H f _Hhom x Nx.
  case Nx as [Hx Hefx].
  case _Hhom; intros Hcart Hhom.
  case (egsym _ _ _ (Hom_preserve_inv _ _ f _Hhom x Hx)).
  case (egsym _ _ _ (Id_droite _ _ (Fermer_inv _ _ (Hcart x Hx)))).
  apply conjonction.
  apply (Fermer_inv _ _ Hx).
  apply (Transpo_gauche G _ _ _ (Hcart x Hx) (Fermer_id _) (Fermer_id _)).
  case (Id_droite _ _ (Hcart x Hx)).
  case Hefx.
  apply egreflexion.
Qed.

Lemma NoyauFermer_id: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  Homomorphisme _ _ f -> Noyau _ _ f (Id H).
Proof.
  intros G H f _Hhom.
  case _Hhom.
  intros Hcart Hhom.
  unfold Noyau.
  case (egsym _ _ _ (IdInv H)).
  case (egsym _ _ _ (Id_gauche H _ (Fermer_inv _ _ (Fermer_id _)))).
  case (egsym _ _ _ (Hhom _ _ (Fermer_id _) (Fermer_inv _ _ (Fermer_id _)))).
  case (egsym _ _ _ (Hom_preserve_inv _ _ f _Hhom _ (Fermer_id _))).
  apply conjonction.
  apply (Fermer_ope _ _ _ (Fermer_id _) (Fermer_inv _ _ (Fermer_id _))).
  apply (Inv_droite _ _ (Hcart _ (Fermer_id _))).
Qed.

Definition NoyauGroupeMelange (G H: Groupe) (f: Tsupp H -> Tsupp G) (Hhom: Homomorphisme _ _ f) :=
  _SousGroupeMelange H (Noyau _ _ f) (SousNoyau _ _ f) (NoyauFermer_ope _ _ f Hhom) (NoyauFermer_inv _ _ f Hhom) (NoyauFermer_id _ _ f Hhom).

Lemma Noyau_SousGroupeNormal: forall (G H: Groupe) (f: Tsupp H -> Tsupp G) 
  (Hhom: Homomorphisme _ _ f), SousGroupeNormal _ (NoyauGroupeMelange _ _ f Hhom).
Proof.
  unfold SousGroupeNormal.
  simpl. unfold Noyau.
  intros G H f _Hhom g h Hg Nh.
  case Nh; intros Hh Hefh.
  apply conjonction.
  apply Fermer_ope.
  - apply Fermer_ope.
  -- apply Hg.
  -- apply Hh.
  -  apply Fermer_inv. apply Hg.
  - case _Hhom; intros Hcart Hhom.
    case (egsym _ _ _ (Hhom _ _ (Fermer_ope _ _ _ Hg Hh) (Fermer_inv _ _ Hg))).
    case (egsym _ _ _ (Hhom _ _ Hg Hh)).
    case Hefh.
    case Id_droite.
  -- apply Hcart. apply Hg.
  -- case (egsym _ _ _ (Hom_preserve_inv _ _ f _Hhom _ Hg)).
     case Inv_droite.
  --- apply Hcart. apply Hg.
  --- apply egreflexion.
Qed.

Definition Image (G H: Groupe) (f: Tsupp H -> Tsupp G): Ensemble (Tsupp G) :=
  fun x => exists h: Tsupp H, et (Supp H h) (egale _ x (f h)).

Lemma ImageSousEnsemble: forall (G H: Groupe) (f: Tsupp H -> Tsupp G),
  SousEnsemble _ (Image _ _ f) (Supp G).
Proof.
  unfold SousEnsemble.  
  intros G H f x Imfx.
  unfold Image in Imfx.
  destruct Imfx as [h Hegxfh].
  case Hegxfh as [Hh Hegxfh].

  

Lemma ImageFermer_ope: forall (G H: Groupe) (f: Tsupp H -> Tsupp G) (Hhom: Homomorphisme _ _ f) (x y: Tsupp G),
  Image _ _ f x -> Image _ _ f y -> Image _ _ f (Ope _ x y).
Proof.
  unfold Image.  
  intros G H f _Hhom x y Imx Imy.
  destruct Imx as [x' Hegxfx'].
  destruct Imy as [y' Hegyfy'].
  exists (Ope _ x' y').
  case Hegxfx' as [Hx' Hegxfx'].
  case Hegyfy' as [Hy' Hegyfy'].
  apply conjonction.
  apply Fermer_ope.
  - apply Hx'.
  - apply Hy'.
  - case _Hhom. intros Hcart Hhom.
    case (egsym _ _ _ (Hhom x' y' Hx' Hy')).
    case Hegxfx', Hegyfy'.
    apply egreflexion.
Qed.

Lemma ImageFermer_inv: forall (G H: Groupe) (f: Tsupp H -> Tsupp G) (Hhom: Homomorphisme _ _ f) (x: Tsupp G),
  Image _ _ f x -> Image _ _ f (Inv _ x).
Proof.
  unfold Image.
  intros G H f _Hhom x Imx.
  destruct Imx as [x' Hegxfx'].
  exists (Inv _ x').
  case Hegxfx' as [Hx' Hegxfx'].
  apply conjonction.
  - apply Fermer_inv. apply Hx'.
  - case _Hhom. intros Hcart Hhom.
    case (egsym _ _ _ (Hom_preserve_inv _ _ f _Hhom _ Hx')).
    case Hegxfx'.
    apply egreflexion.
Qed.

Lemma ImageFermer_id: forall (G H: Groupe) (f: Tsupp H -> Tsupp G) (Hhom: Homomorphisme _ _ f),
  Image _ _ f (Id G).
Proof.
  intros G H f _Hhom.
  unfold Image.
  exists (Id H).
  apply conjonction.
  - apply Fermer_id.
  - case Hom_preserve_id. apply _Hhom. apply egreflexion.
Qed.

Definition ImageSousGroupeMelange (G H: Groupe) (f: Tsupp H -> Tsupp G) :=
  _SousGroupeMelange G (Image _ _ f) (sous) (ImageFermer_ope _ _ f Hhom) (ImageFermer_inv _ _ f Hhom) (ImageFermer_id _ _ f Hhom).

