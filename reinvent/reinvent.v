
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
      (* exclu: forall x, ou (avoir x) (nepas (avoir x)); *)
      eg_ref: forall x, avoir x -> eg x x;
      eg_mission: forall x y, avoir x -> avoir y ->
        eg x y -> forall (P: _ -> Prop), ssi (P x) (P y)
    }.
    Structure taper := Paquet { sorte; _: classe_de sorte }.
    Definition classe (cT: taper) := match cT return classe_de (sorte cT) with
      | Paquet _ c => c
      end.
  End ClasseDef.
  Module Exports.
    (* Coercion sorte: taper >-> Sortclass. *)
    Notation ensembleTaper := taper.
    (* Definition sortee A := match A with
      | Paquet t _ => t
      end. *)
    Definition sortee A := sorte A.
    Definition avoir T := avoir _ (classe T).
    (* Definition avoir A := match classe A with
      | Classe _ a _ _ _ => a
      end. *)
    Definition eg T := eg _ (classe T).
    (* Definition eg A := match classe A with
      | Classe _ _ e _ _ => e
      end. *)
    (* Definition exclu T := exclu _ (classe T). *)
    Definition eg_ref T := eg_ref _ (classe T).
    (* Definition eg_ref (A: ensembleTaper) := match classe A with
      | Classe _ _ _ e' _ => e'
      end. *)
    Definition eg_mission T := eg_mission _ (classe T).
  End Exports.
End Ensemble.
Import Ensemble.Exports.

Section EnsembleTheorie.
  Variable A: ensembleTaper.

  Lemma eg_sym: forall x y, avoir A x -> avoir A y ->
    eg _ x y -> eg _ y x.
  Proof.
    intros x y Ax Ay Exy.
    apply (eg_mission _ _ _ Ax Ay Exy (fun z => eg _ z x)), eg_ref, Ax.
  Qed.

  Lemma eg_trans: forall x y z, avoir A x -> avoir A y -> avoir A z ->
    eg _ x y -> eg _ y z -> eg _ x z.
  Proof.
    intros x y z Ax Ay Az Exy Eyz.
    apply (eg_mission _ _ _ Ax Ay Exy (fun w => eg _ w z)), Eyz.
  Qed.

  Variable T: Type.
  Definition inc (T1 T2: Type) (H: egale _ T1 T2): T1 -> T2 :=
    match H in (egale _ _ T) return (_ -> T) with
    | egreflexion _ _ => (fun x => x)
    end.
  Eval compute in (inc _ _ (egreflexion _ _) nulle).

  Definition f_vide := (fun _: T => Faux).
  Lemma f_vide_exclu: forall (x: T), ou (f_vide x) (nepas (f_vide x)).
  Proof. intros x; apply oudroite; intros F; case F. Qed.
  Definition VideEnsemble :=
    Ensemble.Classe T f_vide (egale T).

  Definition f_meme := (fun _: T => Vraie).
  Lemma f_meme_exclu: forall (x: T), ou (f_meme x) (nepas (f_meme x)).
  Proof. intros x; apply ougauche; apply identite. Qed.
  Definition MemeEnsemble := 
    Ensemble.Classe T f_meme (egale T).

End EnsembleTheorie.

Section CartographieTheorie.
  Variables A B: ensembleTaper.
  Definition Ta := sortee A.
  Definition Tb := sortee B.

  Definition fermer (f: Ta -> Tb) := forall x, avoir A x -> avoir B (f x).
  Definition sousensemble (H: egale _ Ta Tb) := fermer (inc _ _ H).
End CartographieTheorie.

Module Cartographie.
  Section ClasseDef.
    Record classe_de (domaine codomaine: ensembleTaper) := Classe {
      carto: sortee domaine -> sortee codomaine;
      fermer: fermer _ _ carto
    }.  
    Structure taper := Paquet { domaine; codomaine; _: classe_de domaine codomaine }.
    Definition classe (cT: taper) := 
      match cT return classe_de (domaine cT) (codomaine cT) with
      | Paquet _ _ c => c
      end.
  End ClasseDef.
  Module Exports.
    Notation cartoTaper := taper.
    Definition domaine T := domaine T.
    Definition codomaine T := codomaine T.
    Definition carto T := carto _ _ (classe T).
    Definition fermer T := fermer _ _ (classe T).
  End Exports.
End Cartographie.
Import Cartographie.Exports.

Section SousEnsemble.
  Variable A: ensembleTaper.
  Definition sorteA := sortee A.
  Variable confavoir: sorteA -> Prop.
  Variable sous_confavoir: forall x, confavoir x -> avoir A x.
  Lemma sous_eg_ref: forall x, confavoir x -> eg _ x x.
  Proof.
    intros x sAx.
    apply eg_ref. apply sous_confavoir. apply sAx.
  Qed.
  Lemma sous_eg_mission: forall x y, confavoir x -> confavoir y ->
    eg _ x y -> forall (P: _ -> Prop), ssi (P x) (P y).
  Proof.
    intros x y sAx sAy.
    apply eg_mission. apply sous_confavoir. apply sAx.
    apply sous_confavoir. apply sAy.
  Qed.

  Definition produire_sousensemble := Ensemble.Paquet sorteA
    (Ensemble.Classe _ confavoir (eg A) sous_eg_ref sous_eg_mission).
End SousEnsemble.

Section CartographieTheorie.
  Definition injection (f: cartoTaper) :=
    forall (x y: sortee (domaine f)), avoir _ x -> avoir _ y ->
    eg (codomaine f) (carto f x) (carto f y).
  
  Definition surjection (f: cartoTaper) :=
    forall (x: sortee (codomaine f)), avoir _ x ->
    exists x': sortee (domaine f), eg _ x (carto f x').

  Definition bijection (f: cartoTaper) := et (injection f) (surjection f).

  Variable f: cartoTaper.
  Definition imagef_avoir := fun x => et (avoir _ x) (exists x', et (avoir _ x') (eg _ x ((carto f) x'))).
  Lemma imagef_sous: forall x, imagef_avoir x -> avoir (codomaine f) x.
  Proof. 
    unfold imagef_avoir. intros x H.
    case H; intros Ax sAx. apply Ax.
  Qed.
  Definition imageEnsemble := produire_sousensemble (codomaine f) imagef_avoir imagef_sous.
End CartographieTheorie.

Section Nompaire.

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

  Lemma egale_trans: forall (T: Type) (x y z: T),
    egale _ x y -> egale _ y z -> egale _ x z.
  Proof.
    intros T x y z Exy Eyz.
    case Eyz; apply Exy.
  Qed.

  Lemma egale_mission: forall (T: Type) (x y: T), egale _ x y ->
    forall (P: _ -> Prop), ssi (P x) (P y).
  Proof.
    intros T x y Exy P.
    apply conjonction.
    - intros Px. apply (egale_ind _ _ _ Px y Exy).
    - intros Py. apply (egale_ind _ _ _ Py x (egsym _ _ _ Exy)).
  Qed.

  Definition nompaireensemble := Ensemble.Paquet _ (
    Ensemble.Classe naturelle (fun n => estvraie (nompaire n)) (egale naturelle)
    (fun x _ => egreflexion _ x) (fun x y _ _ => egale_mission _ x y)).

  Definition multde4ensemble := Ensemble.Paquet _ (
    Ensemble.Classe naturelle (fun n => estvraie (multde4 n)) (egale naturelle)
    (fun x _ => egreflexion _ x) (fun x y _ _ => egale_mission _ x y)).

  Lemma sous_multde4_nompaire: sousensemble multde4ensemble nompaireensemble (egreflexion _ _).
  Proof.
    unfold sousensemble, Ta. simpl.
    unfold fermer. intros n.
    apply (elimVraie _ _ (impliqP _ _)).
    apply multde4_nompaire.
  Qed.
End Nompaire.

Module Groupe.
  Record melange_de (A: ensembleTaper) := Melange {
    ope: sortee A -> sortee A -> sortee A;
    inv: sortee A -> sortee A;
    id: sortee A;
    fermer_ope: forall x y, avoir A x -> avoir A y -> avoir A (ope x y);
    fermer_inv: forall x, avoir A x -> avoir A (inv x);
    fermer_id: avoir A id;
    assoc_ope: forall x y z, avoir A x -> avoir A y -> avoir A z ->
      eg _ (ope x (ope y z)) (ope (ope x y) z);
    droite_id: forall x, avoir A x -> eg _ x (ope x id);
    gauche_inv: forall x, avoir A x -> eg _ id (ope (inv x) x);
    droite_inv: forall x, avoir A x -> eg _ id (ope x (inv x))
  }.

  Section ClasseDef.
    Record classe_de (A: Type) := Classe {
      base: Ensemble.classe_de A;
      melange: melange_de (Ensemble.Paquet _ base)
    }.
    Structure taper := Paquet { sorte; _: classe_de sorte }.
    Definition classe (cT: taper) :=
      match cT return classe_de (sorte cT) with
      | Paquet _ c => c
      end.
    Definition ensembleTaper (cT: taper) := Ensemble.Paquet (sorte cT) (base _ (classe cT)).
    (* Definition ensembleTaper (cT: taper) :=
      match classe cT return ensembleTaper with
      | Classe _ b _ => Ensemble.Paquet _ b
      end. *)
  End ClasseDef.
  Module Exports.
    Notation groupeTaper := taper.
    Definition sorteg G := sortee (ensembleTaper G).
    (* Definition sorteg G := match G with
      | Paquet t _ => t
      end. *)
    Definition avoirg G := avoir (ensembleTaper G).
    Definition egg G := eg (ensembleTaper G).
    (* Definition exclug G := exclu (ensembleTaper G). *)
    Definition egg_ref G := eg_ref (ensembleTaper G).
    Definition egg_mission G := eg_mission (ensembleTaper G).
    Definition opeg G := ope _ (melange _ (classe G)).
    Definition invg G := inv _ (melange _ (classe G)).
    Definition idg G := id _ (melange _ (classe G)).
    Definition egg_trans G := eg_trans (ensembleTaper G).
    Definition fermer_ope G := fermer_ope _ (melange _ (classe G)).
    Definition fermer_inv G := fermer_inv _ (melange _ (classe G)).
    Definition fermer_id G := fermer_id _ (melange _ (classe G)).
    Definition assoc_ope G := assoc_ope _ (melange _ (classe G)).
    Definition droite_id G := droite_id _ (melange _ (classe G)).
    Definition gauche_inv G := gauche_inv _ (melange _ (classe G)).
    Definition droite_inv G := droite_inv _ (melange _ (classe G)).
  End Exports.
End Groupe.
Import Groupe.Exports. 

Section GroupeTheorie.

  Lemma gauche_id: forall (G: groupeTaper) (x: sorteg G),
    avoirg G x -> egg _ x (opeg _ (idg _) x).
  Proof.
    intros G x Gx.
    pose (eg_mission _ _ _ (fermer_id _)
      (fermer_ope _ _ _ Gx (fermer_inv _ _ Gx)) 
      (droite_inv _ x Gx)
      (fun w => egg _ w x)) as Eex_xxinvx.
    case Eex_xxinvx; intros E1 E2.
    apply (eg_trans _ _ _ _ Gx
      (fermer_ope _ _ _ (fermer_ope _ _ _ Gx (fermer_inv _ _ Gx)) Gx)
      (fermer_ope _ _ _ (fermer_id _) Gx)); simpl.
    - apply (eg_trans _ _ _ _ Gx 
        (fermer_ope _ _ _ Gx (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx))
        (fermer_ope _ _ _ (fermer_ope _ _ _ Gx (fermer_inv _ _ Gx)) Gx)).
    -- apply (eg_trans _ _ _ _ Gx 
        (fermer_ope _ _ _ Gx (fermer_id _)) 
        (fermer_ope _ _ _ Gx (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx))).
    --- apply droite_id, Gx.
    --- pose (eg_mission _ _ _ (fermer_id _)
          (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx)
          (gauche_inv _ _ Gx)
          (fun w => egg _ (opeg _ x (idg G)) (opeg _ x w))) 
          as Exe_xxinvx.
        case Exe_xxinvx; intros E3 E4.
        apply E3. apply egg_ref.
        apply (fermer_ope _ _ _ Gx (fermer_id _)).
    -- apply (assoc_ope _ _ _ _ Gx (fermer_inv _ _ Gx) Gx).
    - pose (eg_mission _ _ _ (fermer_id _)
        (fermer_ope _ _ _ Gx (fermer_inv _ _ Gx))
        (droite_inv _ _ Gx)
        (fun w => egg _ (opeg _ w x) (opeg _ (idg G) x))) 
        as Exxinvx_ex.
      case Exxinvx_ex; intros E5 E6.
      apply E5. apply egg_ref.
      apply fermer_ope. apply fermer_id. apply Gx.
  Qed.

  Lemma gauche_reduire: forall (G: groupeTaper) (x y z: sorteg G),
    avoirg G x -> avoirg _ y -> avoirg _ z ->
    egg _ (opeg _ x y) (opeg _ x z) -> egg _ y z.
  Proof.
    intros G x y z Gx Gy Gz Exy_xz.
    apply (egg_trans _ _ _ _ Gy (fermer_ope _ _ _ (fermer_id _) Gy) Gz).
    - apply gauche_id, Gy.
    - apply (egg_trans _ _ _ _ 
        (fermer_ope _ _ _ (fermer_id _) Gy)
        (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) Gy)
        Gz).
    -- apply (egg_mission _ _ _ (fermer_id _) (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) (gauche_inv _ _ Gx) (fun w => egg _ (opeg _ (idg _) y) (opeg _ w y))).
      apply egg_ref, fermer_ope. apply fermer_id. apply Gy.
    -- apply (egg_trans _ _ _ _
        (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) Gy)
        (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_ope _ _ _ Gx Gy))
        Gz).
    --- apply eg_sym. apply (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_ope _ _ _ Gx Gy)).
        apply (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) Gy).
        apply (assoc_ope _ _ _ _ (fermer_inv _ _ Gx) Gx Gy).
    --- apply (egg_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_ope _ _ _ Gx Gy))
          (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_ope _ _ _ Gx Gz))
          Gz).
    ---- apply (egg_mission _ _ _ (fermer_ope _ _ _ Gx Gy)
          (fermer_ope _ _ _ Gx Gz) Exy_xz
          (fun w => egg _ (opeg _ (invg _ x) (opeg _ x y)) (opeg _ (invg _ x) w))).
        apply egg_ref, fermer_ope. apply fermer_inv, Gx.
        apply fermer_ope. apply Gx. apply Gy.
    ---- apply (egg_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_ope _ _ _ Gx Gz))
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) Gz)
          Gz).
    ----- apply assoc_ope. apply fermer_inv, Gx.
          apply Gx. apply Gz.
    ----- apply (egg_trans _ _ _ _
            (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx) Gz)
            (fermer_ope _ _ _ (fermer_id _) Gz)
            Gz).
    ------ apply (egg_mission _ _ _ 
            (fermer_id _)
            (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx)
            (gauche_inv _ _ Gx)
            (fun w => egg _ (opeg _ w z) (opeg _ (idg G) z))).
          apply eg_ref. apply (fermer_ope _ _ _ (fermer_id _) Gz).
    ------ apply eg_sym. apply Gz. apply fermer_ope. apply fermer_id.
          apply Gz. apply gauche_id. apply Gz.
  Qed.

  Lemma gauche_transpo: forall (G: groupeTaper) (x y z: sorteg G),
    avoirg G x -> avoirg G y -> avoirg G z ->
    egg _ (opeg _ y x) z -> egg _ x (opeg _ (invg _ y) z).
  Proof.
    intros G x y z Gx Gy Gz Eyx_z.
    apply (egg_trans _ _ _ _
      Gx (fermer_ope _ _ _ (fermer_id _) Gx)
      (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gz)).
    - apply gauche_id, Gx.
    - apply (egg_trans _ _ _ _
        (fermer_ope _ _ _ (fermer_id _) Gx)
        (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gy) Gx)
        (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gz)).
    -- apply (eg_mission _ _ _ (fermer_id _)
        (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gy)
        (gauche_inv _ _ Gy)
        (fun w => egg _ (opeg _ (idg _) x) (opeg _ w x))).
      apply eg_ref. apply (fermer_ope _ _ _ (fermer_id _) Gx).
    -- apply (eg_trans _ _ _ _
        (fermer_ope _ _ _ (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gy) Gx)
        (fermer_ope _ _ _ (fermer_inv _ _ Gy) (fermer_ope _ _ _ Gy Gx))
        (fermer_ope _ _ _ (fermer_inv _ _ Gy) Gz)).
    --- apply eg_sym. apply fermer_ope. apply fermer_inv.
        apply Gy. apply fermer_ope. apply Gy. apply Gx.
        apply fermer_ope. apply fermer_ope. apply fermer_inv.
        apply Gy. apply Gy. apply Gx. apply assoc_ope.
        apply fermer_inv. apply Gy. apply Gy. apply Gx.
    --- apply (eg_mission _ _ _
          (fermer_ope _ _ _ Gy Gx)
          Gz Eyx_z
          (fun w => egg _ (opeg _ (invg _ y) w) (opeg _ (invg _ y) z))).
        apply eg_ref. apply fermer_ope. apply fermer_inv, Gy.
        apply Gz.
  Qed.

  Lemma invinv_ident: forall (G: groupeTaper) (x: sorteg G),
    avoirg G x -> egg _ x (invg _ (invg _ x)).
  Proof.
    intros G x Gx.
    apply (gauche_reduire _ _ _ _ (fermer_inv _ _ Gx) Gx
      (fermer_inv _ _ (fermer_inv _ _ Gx))).
    apply (eg_trans _ _ _ _
      (fermer_ope _ _ _ (fermer_inv _ _ Gx) Gx)
      (fermer_id _)
      (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_inv _ _ (fermer_inv _ _ Gx)))).
    - apply eg_sym. apply fermer_id. apply fermer_ope.
      apply fermer_inv. apply Gx. apply Gx.
      apply gauche_inv. apply Gx.
    - apply droite_inv. apply fermer_inv. apply Gx.
  Qed.

  Lemma invop_opinvinv: forall (G: groupeTaper) (x y: sorteg G),
    avoirg G x -> avoirg G y ->
    egg _ (invg _ (opeg _ x y)) (opeg _ (invg _ y) (invg _ x)).
  Proof.
    intros G x y Gx Gy.
    apply gauche_transpo.
    - apply fermer_inv. apply fermer_ope. apply Gx. apply Gy.
    - apply Gy.
    - apply fermer_inv, Gx.
    - apply (eg_trans _ _ _ _
        (fermer_ope _ _ _ Gy (fermer_inv _ _ (fermer_ope _ _ _ Gx Gy)))
        (fermer_ope _ _ _ (fermer_inv _ _ Gx) (fermer_id _))
        (fermer_inv _ _ Gx)).
    -- apply gauche_transpo. apply fermer_ope.
      apply Gy. apply fermer_inv. apply fermer_ope.
      apply Gx. apply Gy. apply Gx. apply fermer_id.
      apply (eg_trans _ _ _ _
        (fermer_ope _ _ _ Gx (fermer_ope _ _ _ Gy (fermer_inv _ _ (fermer_ope _ _ _ Gx Gy))))
        (fermer_ope _ _ _ (fermer_ope _ _ _ Gx Gy) (fermer_inv _ _ (fermer_ope _ _ _ Gx Gy)))
        (fermer_id _)).
    --- apply assoc_ope. apply Gx. apply Gy.
        apply fermer_inv. apply fermer_ope.
        apply Gx. apply Gy.
    --- apply eg_sym. apply fermer_id. apply fermer_ope.
        apply fermer_ope. apply Gx. apply Gy.
        apply fermer_inv. apply fermer_ope.
        apply Gx. apply Gy.
        apply droite_inv. apply fermer_ope.
        apply Gx. apply Gy.
    -- apply eg_sym. apply fermer_inv.
      apply Gx. apply fermer_ope. apply fermer_inv.
      apply Gx. apply fermer_id. apply droite_id.
      apply fermer_inv. apply Gx.
  Qed.

  Lemma id_invid: forall (G: groupeTaper), egg _ (idg G) (invg _ (idg G)).
  Proof.
    intros G.
    apply (eg_trans _ _ _ _
      (fermer_id _)
      (fermer_ope _ _ _ (fermer_inv _ _ (fermer_id _)) (fermer_id _))
      (fermer_inv _ _ (fermer_id _))).
    - apply gauche_transpo. apply fermer_id.
      apply fermer_id. apply fermer_id.
      apply eg_sym. apply fermer_id. apply fermer_ope.
      apply fermer_id. apply fermer_id.
      apply droite_id. apply fermer_id.
    - apply eg_sym. apply fermer_inv.
      apply fermer_id. apply fermer_ope.
      apply fermer_inv. apply fermer_id.
      apply fermer_id. apply droite_id.
      apply fermer_inv. apply fermer_id.
  Qed.

End GroupeTheorie.

Definition homomorphisme (dom codom: groupeTaper) (f: sorteg dom -> sorteg codom) :=
  forall x y, avoirg dom x -> avoirg dom y ->
  egg _ (f (opeg _ x y)) (opeg _ (f x) (f y)).

Module Homomorphisme.
  Section ClasseDef.
    Record classe_de (dom codom: groupeTaper) := Classe {
      base: Cartographie.classe_de (Groupe.ensembleTaper dom) (Groupe.ensembleTaper codom);
      hom: homomorphisme _ _ (carto (Cartographie.Paquet _ _ base))
    }.
    Structure taper := Paquet { domaine; codomaine; _: classe_de domaine codomaine }.
    Definition classe (cT: taper) :=
      match cT return classe_de (domaine cT) (codomaine cT) with
      | Paquet _ _ c => c
      end.
    Definition cartoTaper (cT: taper) := Cartographie.Paquet _ _ (base _ _ (classe cT)).
  End ClasseDef.
  Module Exports.
    Notation homTaper := taper.
    Definition domTaper T := sorteg (domaine T).
    Definition codomTaper T := sorteg (codomaine T).
    Definition domf T := domaine T.
    Definition codomf T := codomaine T.
    Definition carte T := carto (Cartographie.Paquet _ _ (base _ _ (classe T))).
    Definition hom T := hom _ _ (classe T).
    Definition fermf T := fermer (Cartographie.Paquet _ _ (base _ _ (classe T))).
    Definition hom_as_carto T := Cartographie.Paquet _ _ (base _ _ (classe T)).
  End Exports.
End Homomorphisme.
Import Homomorphisme.Exports.

Section HomomorphismeTheorie.
  Lemma hom_preserve_id: forall (f: homTaper), egg _ (idg (codomf f)) ((carte f) (idg (domf f))).
  Proof.
    intros f.
    pose (fermf _ _ (fermer_id (domf f))) as Gfe.
    apply (gauche_reduire _ _ _ _
      Gfe (fermer_id _) Gfe).
    apply (eg_trans _ _ _ _
      (fermer_ope _ _ _ Gfe (fermer_id (codomf f)))
      Gfe (fermer_ope _ _ _ Gfe Gfe)).
    - apply eg_sym. apply Gfe. apply fermer_ope. apply Gfe.
      apply fermer_id. apply droite_id. apply Gfe.
    - apply (eg_trans _ _ _ _
        Gfe
        (fermf _ _ (fermer_ope _ _ _ (fermer_id (domf f)) (fermer_id _)))
        (fermer_ope _ _ _ Gfe Gfe)).
    -- apply (eg_mission _ _ _
        (fermer_id _) (fermer_ope _ _ _ (fermer_id _) (fermer_id _))
        (droite_id _ _ (fermer_id _))
        (fun w => egg _ ((carte f) (idg (domf f))) ((carte f) w))).
      apply eg_ref. apply Gfe.
    -- apply hom. apply fermer_id. apply fermer_id.
  Qed.

  Lemma hom_preserve_inv: forall (f: homTaper) (x: domTaper f),
    avoirg (domf f) x -> egg _ ((carte f) (invg _ x)) (invg _ ((carte f) x)).
  Proof.
    intros f x Hx.
    pose (fermf _ _ Hx) as Gfx.
    pose (fermf _ _ (fermer_inv _ _ Hx)) as Gfxinv.
    apply (eg_trans _ _ _ _
      Gfxinv
      (fermer_ope _ _ _ (fermer_inv _ _ Gfx) (fermer_id _))
      (fermer_inv _ _ Gfx)).
    - apply gauche_transpo. apply Gfxinv.
      apply Gfx. apply fermer_id.
      apply (eg_trans _ _ _ _
        (fermer_ope _ _ _ Gfx Gfxinv)
        (fermf _ _ (fermer_ope _ _ _ Hx (fermer_inv _ _ Hx)))
        (fermer_id _)).
    -- apply eg_sym. apply fermf. apply fermer_ope.
      apply Hx. apply fermer_inv. apply Hx.
      apply fermer_ope. apply fermf. apply Hx.
      apply fermf. apply fermer_inv. apply Hx.
      apply hom. apply Hx. apply fermer_inv.
      apply Hx.
    -- apply (eg_trans _ _ _ _
        (fermf _ _ (fermer_ope _ _ _ Hx (fermer_inv _ _ Hx)))
        (fermf _ _ (fermer_id _))
        (fermer_id _)).
    --- apply eg_sym. apply fermf. apply fermer_id.
        apply fermf. apply fermer_ope. apply Hx.
        apply fermer_inv. apply Hx.
        apply (eg_mission _ _ _
          (fermer_id _)
          (fermer_ope _ _ _ Hx (fermer_inv _ _ Hx))
          (droite_inv _ _ Hx)
          (fun w => egg _ ((carte f) (idg (domf f))) ((carte f) w))).
        apply eg_ref. apply fermf. apply fermer_id.
    --- apply eg_sym. apply fermer_id. apply fermf. apply fermer_id.
        apply hom_preserve_id.
    - apply eg_sym. apply fermer_inv. apply fermf. apply Hx.
      apply fermer_ope. apply fermer_inv. apply fermf.
      apply Hx. apply fermer_id. apply droite_id.
      apply fermer_inv. apply fermf. apply Hx.
  Qed.
End HomomorphismeTheorie.

Section SousGroupe.
  Variable G H: groupeTaper.
  Definition Gtaper := sorteg G.
  Definition Htaper := sorteg H.
  Variable Eghtaper: egale _ Htaper Gtaper.
  Definition i := inc _ _ Eghtaper.
  Definition sousgroupe := homomorphisme H G i.

  Definition sousgroupenormal :=
    forall (g: sorteg G) (h: sorteg H), avoirg _ g -> avoirg _ h ->
    exists h', et (avoirg H h') (egg _ (i h') (opeg _ (opeg _ g (i h)) (invg _ g))).
End SousGroupe.
Section Noyau.
  Variable f: homTaper.
  Definition H := domf f.
  Definition Hens := Groupe.ensembleTaper H.
  Definition G := codomf f.
  Definition hTaper := sorteg H.
  Definition noyauf_avoir := fun (x: hTaper) => et (avoir Hens x) (egg G (idg _) ((carte f) x)).
  Lemma noyauf_sous: forall x, noyauf_avoir x -> avoirg _ x.
  Proof.
    unfold noyauf_avoir. intros x H0. case H0; intros H1 H2. apply H1.
  Qed.
  Definition noyauEnsemble := produire_sousensemble _ noyauf_avoir noyauf_sous.
  Lemma noyau_fermer_ope: forall x y, avoir noyauEnsemble x -> avoir noyauEnsemble y ->
    avoir noyauEnsemble (opeg _ x y).
  Proof.
    unfold noyauf_avoir. intros x y Hx Hy.
    case Hx; intros Hx1 Hx2. case Hy; intros Hy1 Hy2.
    apply conjonction.
    - apply fermer_ope. apply Hx1. apply Hy1.
    - apply (eg_trans _ _ _ _
        (fermer_id _)
        (fermer_ope _ _ _ (fermer_id _) (fermer_id _))
        (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    -- apply droite_id. apply fermer_id.
    -- apply (eg_trans _ _ _ _
         (fermer_ope _ _ _ (fermer_id _) (fermer_id _))
         (fermer_ope _ _ _ (fermer_id _) (fermf _ _ Hy1))
         (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    --- apply (eg_mission _ _ _
          (fermer_id _) (fermf _ _ Hy1)
          Hy2
          (fun w => egg _ (opeg _ (idg _) (idg _)) (opeg _ (idg _) w))).
        apply eg_ref. apply fermer_ope. apply fermer_id. apply fermer_id.
    --- apply (eg_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_id _) (fermf _ _ Hy1))
          (fermer_ope _ _ _ (fermf _ _ Hx1) (fermf _ _ Hy1))
          (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    ---- apply (eg_mission _ _ _
           (fermer_id _) (fermf _ _ Hx1)
           Hx2
           (fun w => egg _ (opeg _ (idg _) ((carte f) y)) (opeg _ w ((carte f) y)))).
          apply eg_ref. apply fermer_ope. apply fermer_id. apply fermf. apply Hy1.
    ---- apply eg_sym. apply fermf. apply fermer_ope. apply Hx1. apply Hy1.
         apply fermer_ope. apply fermf. apply Hx1. apply fermf. apply Hy1.
         apply hom. apply Hx1. apply Hy1.
  Qed.     
  Lemma noyau_fermer_inv: forall x, avoir noyauEnsemble x ->
    avoir noyauEnsemble (invg _ x).
  Proof.
    intros x Hx. case Hx; intros Hx1 Hx2.
    apply conjonction.
    - apply fermer_inv. apply Hx1.
    - apply (eg_trans _ _ _ _
        (fermer_id _)
        (fermer_inv _ _ (fermer_id _))
        (fermf _ _ (fermer_inv _ _ Hx1))).
    -- apply id_invid.
    -- apply (eg_trans _ _ _ _
         (fermer_inv _ _ (fermer_id _))
         (fermer_inv _ _ (fermf _ _ Hx1))
         (fermf _ _ (fermer_inv _ _ Hx1))).
    --- apply (eg_mission _ _ _
          (fermer_id _)
          (fermf _ _ Hx1)
          Hx2
          (fun w => egg _ (invg _ (idg _)) (invg _ w))).
        apply eg_ref. apply fermer_inv. apply fermer_id.
    --- apply eg_sym. apply fermf. apply fermer_inv. apply Hx1.
        apply fermer_inv. apply fermf. apply Hx1.
        apply hom_preserve_inv. apply Hx1.
  Qed. 
  Lemma noyau_fermer_id: avoir noyauEnsemble (idg _).
  Proof.
    apply conjonction.
    - apply fermer_id.
    - apply hom_preserve_id.
  Qed.
  Definition noyauGroupe := Groupe.Paquet (sortee noyauEnsemble) (Groupe.Classe (sortee noyauEnsemble)
    (Ensemble.classe noyauEnsemble) (Groupe.Melange noyauEnsemble (opeg H) (invg _ ) (idg _)
      noyau_fermer_ope noyau_fermer_inv noyau_fermer_id
      (fun x y z Hx Hy Hz => assoc_ope _ _ _ _ (noyauf_sous _ Hx) (noyauf_sous _ Hy) (noyauf_sous _ Hz))
      (fun x Hx => droite_id _ _ (noyauf_sous _ Hx))
      (fun x Hx => gauche_inv _ _ (noyauf_sous _ Hx))
      (fun x Hx => droite_inv _ _ (noyauf_sous _ Hx)))).
  Lemma noyau_sousgroupenormal: sousgroupenormal H noyauGroupe (egreflexion _ _).
  Proof.
    unfold sousgroupenormal. simpl.
    intros g h Hg Nh. exists (opeg _ (opeg _ g h) (invg _ g)).
    pose (noyauf_sous _ Nh) as Hh. apply conjonction. 
    - unfold noyauGroupe. unfold noyauEnsemble. unfold noyauf_avoir.
      unfold avoirg. unfold Groupe.ensembleTaper. 
      unfold avoir. simpl. apply conjonction.
    -- apply fermer_ope. apply fermer_ope. apply Hg.
       apply Nh. apply fermer_inv. apply Hg.
    -- apply (eg_trans _ _ _ _
         (fermer_id _)
         (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_inv _ _ (fermf _ _ Hg)))
         (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    --- apply droite_inv. apply fermf. apply Hg.
    --- apply (eg_trans _ _ _ _
          (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ---- apply (eg_mission _ _ _
           (fermf _ _ Hg) (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _))
           (droite_id _ _ (fermf _ _ Hg))
           (fun w => egg _ (opeg _ ((carte f) g) (invg _ ((carte f) g))) (opeg _ w (invg _ ((carte f) g))))).
         apply eg_ref. apply fermer_ope. apply fermf. apply Hg. apply fermer_inv.
         apply fermf. apply Hg.
    ---- apply (eg_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ----- case Nh; intros Nh0 Eefh.
          apply (eg_mission _ _ _
                  (fermer_id _) (fermf _ _ Hh)
                  Eefh
                  (fun w => egg _ (opeg _ (opeg _ ((carte f) g) (idg _)) (invg _ ((carte f) g)))
                                  (opeg _ (opeg _ ((carte f) g) w) (invg _ ((carte f) g))))).
          apply eg_ref. apply fermer_ope. apply fermer_ope. apply fermf. apply Hg.
          apply fermer_id. apply fermer_inv. apply fermf. apply Hg.
    ----- apply (eg_trans _ _ _ _
            (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).                                  
    ------ apply eg_sym. apply fermer_ope. apply fermf. apply fermer_ope.
           apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
           apply fermer_ope. apply fermer_ope. apply fermf. apply Hg.
           apply fermf. apply Hh. apply fermer_inv. apply fermf. apply Hg. 
           apply (eg_mission _ _ _
             (fermf _ _ (fermer_ope _ _ _ Hg Hh)) 
             (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh))
             (hom f _ _ Hg Hh)
             (fun w => egg _ (opeg _ ((carte f) (opeg _ g h)) (invg _ ((carte f) g)))
                             (opeg _ w (invg _ ((carte f) g))))).
           apply eg_ref. apply fermer_ope. apply fermf. apply fermer_ope.
           apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
    ------ apply (eg_trans _ _ _ _
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermf _ _ (fermer_inv _ _ Hg)))
            (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ------- apply eg_sym. apply fermer_ope. apply fermf. apply fermer_ope.
            apply Hg. apply Hh. apply fermf. apply fermer_inv. apply Hg.
            apply fermer_ope. apply fermf. apply fermer_ope. apply Hg. apply Hh.
            apply fermer_inv. apply fermf. apply Hg.
            apply (eg_mission _ _ _
              (fermf _ _ (fermer_inv _ _ Hg))
              (fermer_inv _ _ (fermf _ _ Hg))
              (hom_preserve_inv _ _ Hg)
              (fun w => egg _ (opeg _ ((carte f) (opeg _ g h)) w)
                              (opeg _ ((carte f) (opeg _ g h)) (invg _ ((carte f) g))))).      
            apply eg_ref. apply fermer_ope. apply fermf. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
    ------- apply eg_sym. apply fermf. apply fermer_ope. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply Hg. apply fermer_ope.
            apply fermf. apply fermer_ope. apply Hg. apply Hh. apply fermf.
            apply fermer_inv. apply Hg. apply hom. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply Hg.
    - apply eg_ref. apply (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)).
Qed.
End Noyau.

Section Image.
  Variable f: homTaper.
  Definition phi := carte f.
  Definition Imf := imageEnsemble (Homomorphisme.cartoTaper f).
  Lemma image_fermer_ope: forall x y, avoir Imf x -> avoir Imf y ->
    avoir Imf (opeg _ x y).
  Proof.
    intros x y Imx Imy.
    destruct Imx as [Gx H0]. destruct H0 as [x' H1].
    destruct H1 as [Hx' xfx'].
    destruct Imy as [Gy H0]. destruct H0 as [y' H1].
    destruct H1 as [Hy' yfy'].
    apply conjonction.
    - apply fermer_ope. apply Gx. apply Gy.
    - exists (opeg _ x' y'). apply conjonction.
    -- apply fermer_ope. apply Hx'. apply Hy'.
    -- apply (eg_trans _ _ _ _
         (fermer_ope _ _ _ Gx Gy)
         (fermer_ope _ _ _ (fermf _ _ Hx') Gy)
         (fermf _ _ (fermer_ope _ _ _ Hx' Hy'))).
    --- apply (eg_mission _ _ _
          Gx (fermf _ _ Hx') xfx' 
          (fun w => egg _ (opeg _ x y) (opeg _ w y))).
        apply eg_ref. apply (fermer_ope _ _ _ Gx Gy).
    --- apply (eg_trans _ _ _ _
          (fermer_ope _ _ _ (fermf _ _ Hx') Gy)
          (fermer_ope _ _ _ (fermf _ _ Hx') (fermf _ _ Hy'))
          (fermf _ _ (fermer_ope _ _ _ Hx' Hy'))).
    ---- apply (eg_mission _ _ _
           Gy (fermf _ _ Hy') yfy' 
           (fun w => egg _ (opeg _ (phi x') y) (opeg _ (phi x') w))).
         apply eg_ref. apply (fermer_ope _ _ _ (fermf _ _ Hx') Gy).
    ---- apply eg_sym. apply fermf. apply fermer_ope. apply Hx'. 
         apply Hy'. apply fermer_ope. apply fermf. apply Hx'. 
         apply fermf. apply Hy'.
         apply hom. apply Hx'. apply Hy'.
  Qed.
  Lemma image_fermer_inv: forall x, avoir Imf x ->
    avoir Imf (invg _ x).
  Proof.
    intros x Imx. destruct Imx as [Gx H0]. destruct H0 as [x' H1].
    destruct H1 as [Hx' xfx']. apply conjonction.
    - apply fermer_inv. apply Gx.
    - exists (invg _ x'). apply conjonction.
    -- apply fermer_inv. apply Hx'.
    -- apply (eg_trans _ _ _ _
         (fermer_inv _ _ Gx)
         (fermer_inv _ _ (fermf _ _ Hx'))
         (fermf _ _ (fermer_inv _ _ Hx'))).
    --- apply (eg_mission _ _ _
          Gx (fermf _ _ Hx') xfx'
          (fun w => egg _ (invg _ x) (invg _ w))).
        apply eg_ref. apply (fermer_inv _ _ Gx).
    --- apply eg_sym. apply (fermf _ _ (fermer_inv _ _ Hx')).
        apply (fermer_inv _ _ (fermf _ _ Hx')).
        apply hom_preserve_inv. apply Hx'.
  Qed.
  Lemma image_fermer_id: avoir Imf (idg _).
  Proof.
    apply conjonction.
    - apply fermer_id.
    - exists (idg _). apply conjonction.
    -- apply fermer_id.
    -- apply hom_preserve_id.
  Qed.
  Definition imageGroupe := Groupe.Paquet (sortee Imf) (Groupe.Classe (sortee Imf)
  (Ensemble.classe Imf) (Groupe.Melange Imf (opeg (codomf f)) (invg _ ) (idg _)
    image_fermer_ope image_fermer_inv image_fermer_id
    (fun x y z Hx Hy Hz => assoc_ope _ _ _ _ (imagef_sous _ _ Hx) (imagef_sous _ _ Hy) (imagef_sous _ _ Hz))
    (fun x Hx => droite_id _ _ (imagef_sous _ _ Hx))
    (fun x Hx => gauche_inv _ _ (imagef_sous _ _ Hx))
    (fun x Hx => droite_inv _ _ (imagef_sous _ _ Hx)))).
End Image.

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

