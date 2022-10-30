Section Logique.
  Section Propositionnelle.
    Inductive Vraie : Prop := identite : Vraie.
    Inductive Faux : Prop := .
    Inductive et (A B:Prop) : Prop := 
      conjonction : A -> B -> et A B.
    Inductive ou (A B:Prop) : Prop :=
      | ou_gauche : A -> ou A B
      | ou_droite : B -> ou A B.
    Definition nepas (A:Prop) := A -> Faux.
    Definition ssi (A B:Prop) := et (A -> B) (B -> A).

    Definition et_prj1 {A B:Prop} (H: et A B) :=
      match H with
        | conjonction _ _ a _ => a
      end.
    Definition et_prj2 {A B:Prop} (H: et A B) :=
      match H with
        | conjonction _ _ _ b => b
      end. 

    Lemma ssi_ref : forall {A:Prop}, ssi A A.
    Proof. intros A; apply conjonction; intros HA; apply HA. Qed.
    Lemma ssi_sym : forall {A B:Prop}, ssi A B -> ssi B A.
    Proof. intros A B AB; apply conjonction. apply (et_prj2 AB). apply (et_prj1 AB). Qed.
    Lemma ssi_trans : forall {A B C:Prop}, ssi A B -> ssi B C -> ssi A C.
    Proof. intros A B C AB BC; apply conjonction.
      - intros HA. apply ((et_prj1 BC) ((et_prj1 AB) HA)).
      - intros HC. apply ((et_prj2 AB) ((et_prj2 BC) HC)).
    Qed.
    Definition absurde (A C:Prop) (HA:A) (HnA:nepas A) := Faux_ind C (HnA HA).
    Lemma contrad : forall {A B:Prop}, (A -> B) -> (nepas B -> nepas A).
    Proof. intros A B AB HnB HA; apply (HnB (AB HA)). Qed.
    Lemma nepas_ssi_compat : forall {A B:Prop}, ssi A B -> ssi (nepas A) (nepas B).
    Proof. intros A B AB. apply conjonction; apply contrad. apply (et_prj2 AB). apply (et_prj1 AB). Qed.
  End Propositionnelle.
  Section PremierOrdre.
    Inductive remplie {T:Type} (P: T -> Prop) : Prop :=
      exiter : forall x, P x -> remplie P.
    Context {T:Prop} {P: T -> Prop}.
    Definition ex_prj1 (H: remplie P):=
      match H with exiter _ a _ => a end.
    (* This returns independent type, so one has to let H be free. *)
    Definition ex_prj2 (H: remplie P) :=
      match H return P (ex_prj1 H) with exiter _ _ Pa => Pa end.
  End PremierOrdre.
  Section Egalite.
    Inductive egale {A:_} (x:A) : A -> Prop :=
      | egale_ref : egale x x.
    Axiom egale_fonc : forall {A:Type} {B: A -> Type} (f g: forall x:A, B x),
      (forall x: A, egale (f x) (g x)) -> egale f g.
    Definition f_egale {A B:_} (f: A -> B) {x y:A} (H: egale x y) :=
      egale_ind _ _ (fun w => egale (f x) (f w)) (egale_ref (f x)) y H.
    Definition egale_sym {A:_} {x y:A} (H: egale x y) :=
      egale_ind _ _ (fun w => egale w x) (egale_ref x) _ H.
    Definition egale_trans {A:_} {x y z:A} (Exy: egale x y) (Eyz: egale y z) :=
      egale_ind _ _ (egale x) Exy _ Eyz.
  End Egalite.
  Section Habitee.
    Inductive habitee (A:_) : Prop :=
      habit : A -> habitee A.
    Definition remplie_habitee {A:_} (P: A -> Prop) (HP: remplie P) :=
      match HP with exiter _ x _ => habit _ x end.
    Definition habitee_covar {A B:_} (P: A -> B) (hA: habitee A) :=
      match hA with habit _ a => habit _ (P a) end.
  End Habitee.
End Logique.
Section Booleenne.
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
  Definition egbvraie := egb vraie.
  Definition estvraie b :=
    match b with
    | vraie => Vraie
    | faux => Faux
    end.
  Definition estfaux b := estvraie (nepasb b).
End Booleenne.
Section Refleter.
  Inductive refleter (P:Prop) : booleenne -> Set :=
    | refleter_vraie : P -> refleter P vraie
    | refleter_faux : nepas P -> refleter P faux.
  Definition ssiP {P Q b} (HPb: refleter P b) (HPQ: ssi P Q) :=
    match HPb with
      | refleter_vraie _ p => refleter_vraie Q (et_prj1 HPQ p)
      | refleter_faux _ n => refleter_faux Q (et_prj1 (nepas_ssi_compat HPQ) n)
    end.
  Definition idP {b} :=
    match b return refleter (estvraie b) b with
      | vraie => refleter_vraie _ identite
      | faux => refleter_faux _ (Faux_ind Faux)
    end.
  Definition egb_egale {b1 b2} :=
    match b1, b2 return refleter (egale b1 b2) (egb b1 b2) with
      | vraie, vraie => refleter_vraie _ (egale_ref vraie)
      | vraie, faux => refleter_faux _ (egale_ind _ vraie estvraie identite faux)
      | faux, vraie => refleter_faux _ (egale_ind _ faux estfaux identite vraie)
      | faux, faux => refleter_vraie _ (egale_ref faux)
    end.
  Definition vraie_redondant {b} := conjonction _ _
    match b return estvraie b -> estvraie (egb vraie b) with
      | vraie => fun _ => identite
      | faux => Faux_ind Faux
    end
    match b return estvraie (egb vraie b) -> estvraie b with
      | vraie => fun _ => identite
      | faux => Faux_ind Faux
    end.
  Definition casProp flag P := match flag with vraie=>P | faux=> nepas P end.
  Definition introVraieFaux {P flag b} (HPb: refleter P b) :=
    match flag, HPb in refleter _ c return casProp flag P -> estvraie (egb flag c) with
      | vraie, refleter_vraie _ p => fun _ => identite
      | vraie, refleter_faux _ n => n
      | faux, refleter_vraie _ p => fun HnP => Faux_ind _ (HnP p)
      | faux, refleter_faux _ n => fun _ => identite
      end.
  Definition elimVraieFaux {P flag b} (HPb: refleter P b) :=
    match HPb in refleter _ c, flag return (estvraie (egb flag c) -> casProp flag P) with
      | refleter_vraie _ p, vraie => fun _ => p
      | refleter_vraie _ p, faux => Faux_ind _
      | refleter_faux _ n, vraie => Faux_ind _
      | refleter_faux _ n, faux => fun _ => n
    end.
  Definition elimVraie {P b} (HPb: refleter P b) (Hb: estvraie b) :=
    elimVraieFaux HPb (et_prj1 vraie_redondant Hb).
  Definition introVraie {P b} (HPb: refleter P b) (HP:P) :=
    (et_prj2 vraie_redondant) (introVraieFaux(flag:=vraie) HPb HP).
  
  Lemma impliqP: forall b1 b2, refleter (estvraie b1 -> estvraie b2) (impliqb b1 b2).
  Proof.
    intros b1 b2; case b1, b2.
    - apply refleter_vraie. intros. apply identite.
    - apply refleter_faux. intros F. apply F, identite.
    - apply refleter_vraie. intros F; case F.
    - apply refleter_vraie. intros F; apply F.
  Qed.
End Refleter.
Section ProduitDirect.
  Inductive produit (A B:_) : Type :=
    | paire : A -> B -> produit A B.
  Definition premiere {A B} (p: produit A B) :=
    match p with paire _ _ x _ => x end.
  Definition deuxieme {A B} (p: produit A B) :=
    match p with paire _ _ _ y => y end.
End ProduitDirect.
Section Naturelle.
  Inductive naturelle : Set :=
    | nulle : naturelle
    | succ : naturelle -> naturelle.
  Fixpoint ajouter n m {struct n} :=
    match n with
      | nulle => m
      | succ n' => succ (ajouter n' m)
    end.
  Fixpoint soustraire n m :=
    match n, m with
      | nulle, _ => nulle
      | _, nulle => n
      | succ n', succ m' => soustraire n' m'
    end.
  Fixpoint multiplier n m :=
    match n with
      | nulle => nulle
      | succ n' => ajouter m (multiplier n' m)
    end.
  Fixpoint _diviser x y q u :=
    match x with
      | nulle => paire _ _ q u
      | succ x' =>
        match u with
          | nulle => _diviser x' y (succ q) y
          | succ u' => _diviser x' y q u'
        end
    end.
  Definition quotient x y :=
    match y with
      | nulle => nulle
      | succ y' => premiere (_diviser x y' nulle y')
    end.
  Definition modulo x y :=
    match y with
      | nulle => nulle
      | succ y' => deuxieme (_diviser x y' nulle y')
    end.
  Definition predecesseur n :=
    match n with
      | nulle => nulle
      | succ n' => n'
    end.
  Definition egale_succ {n m} (H: egale (succ n) (succ m)) : egale n m
    := f_egale predecesseur H.

  Lemma egale_sousnulle : forall n m, egale n m -> egale nulle (soustraire n m).
  Proof. induction n, m; intros H; try apply egale_ref; try apply egale_sym, H; try apply IHn, egale_succ, H. Qed.
  Lemma addNS : forall n, egale n (succ n) -> Faux.
  Proof.
    induction n.
    -- apply (egale_ind _ nulle (fun n => match n with |nulle => Vraie | _ => Faux end) identite (succ nulle)).
    -- intros H; apply (IHn (egale_succ H)).
  Qed.
End Naturelle.
Module Egtaper.
  Section ClasseDef.
    Record classe_de (T:Type) := Classe {
      op: T -> T -> booleenne;
      ref: forall x y, refleter (egale x y) (op x y)
    }.
    Structure taper := Paquet { sorte; _: classe_de sorte }.
    Definition classe (cT:taper) :=
      match cT return classe_de (sorte cT) with Paquet _ c => c end.
  End ClasseDef.
  Module Exports.
    Coercion sorte: taper >-> Sortclass.
    Notation egTaper := taper.
    Definition egop {T} := op _ (classe T).
  End Exports.
End Egtaper.
Import Egtaper.Exports.
Section EgtaperTheorie.
  Definition egP {T:egTaper} :=
    match T return forall x y:T, refleter (egale x y) (egop x y) with
    Egtaper.Paquet _ (Egtaper.Classe _ _ ref') => ref' end.
End EgtaperTheorie.
Section EgNaturelle.
  Fixpoint egnat n m :=
    match n, m with
    | nulle, nulle => vraie
    | nulle, succ _ => faux
    | succ _, nulle => faux
    | succ n', succ m' => egnat n' m'
    end.
  Lemma egale_egnatP : forall n m, refleter (egale n m) (egnat n m).
  Proof.
    induction n; induction m.
    - apply refleter_vraie, egale_ref.
    - apply refleter_faux; unfold nepas. apply (egale_ind _ nulle (fun n => match n with |nulle => Vraie |_ => Faux end) identite (succ m)).
    - apply refleter_faux; unfold nepas. apply (egale_ind _ (succ n) (fun n => match n with |succ _ => Vraie |nulle => Faux end) identite nulle).
    - apply (ssiP(P:= egale n m)). apply IHn. apply conjonction.
      apply f_egale. apply egale_succ.
  Qed.

  Definition trois := succ (succ (succ nulle)).
  Definition neuf := Eval compute in multiplier trois trois.
  Definition dix := Eval compute in succ neuf.
  Definition naturelle_egTaper := Egtaper.Paquet _ (Egtaper.Classe naturelle egnat egale_egnatP).
  Canonical Structure naturelle_egTaper.
  Lemma egvraie_estvraie : forall b, egale vraie b -> estvraie b.
  Proof. intros b H. case H. apply identite. Qed.
  Lemma estvraie_egvraie : forall b, estvraie b -> egale vraie b.
  Proof. intros b; case b; intros H. apply egale_ref. apply Faux_ind, H. Qed.
  Definition neufNdix (H: egale neuf dix) :=
    Eval compute in (egale_ind _ (egop neuf dix) estfaux
    identite vraie (egale_sym (estvraie_egvraie _ (introVraie (egP neuf dix) H)))).
End EgNaturelle.
Section Ensemble.
  Context {T:Type}.
  Definition Ensemble := T -> Prop.
  Definition videEnsemble : Ensemble := fun _ => Faux.
  Definition memeEnsemble : Ensemble := fun _ => Vraie.
  Definition sous (B A:Ensemble) := forall x, B x -> A x.
  Definition syndicat (A B:Ensemble) : Ensemble :=
    fun x => ou (A x) (B x).
  Definition intsec (A B:Ensemble) : Ensemble :=
    fun x => et (A x) (B x).
  Definition compl (A:Ensemble) : Ensemble :=
    fun x => nepas (A x).
  Definition seul x : Ensemble := egale x.
  Axiom egale_ens : forall A B, et (sous A B) (sous B A) -> egale A B.
End Ensemble.
Section Cartographie.
  Context {T1 T2:Type} (A:@Ensemble T1) (B:@Ensemble T2) (f:T1 -> T2).
  Definition image : Ensemble := fun y => exists x, egale y (f x).
  Definition iminv : Ensemble := fun x => B (f x).
  Definition carto := forall x, A x -> B (f x).
End Cartographie.
Section Cartographie.
  Context {T1 T2:Type} {A:@Ensemble T1} {B:@Ensemble T2} {f: T1 -> T2}.
  Definition inject (Hf: carto A B f) :=
    forall x1 x2, egale (f x1) (f x2) -> egale x1 x2.
  Definition surject (Hf: carto A B f) :=
    forall y, B y -> exists x, egale y (f x).
  Definition biject (Hf: carto A B f) :=
    et (inject Hf) (surject Hf).
End Cartographie.
Module Groupe.
  Section ClasseDef.
    Record classe_de {T:Type} := Classe {
      avoir : Ensemble;
      op: T -> T -> T;
      inv: T -> T;
      id: T;
      ferm_op: forall x y, avoir x -> avoir y -> avoir (op x y);
      ferm_inv: forall x, avoir x -> avoir (inv x);
      ferm_id: avoir id;
      assoc_op: forall x y z, avoir x -> avoir y -> avoir z ->
        egale (op x (op y z)) (op (op x y) z);
      droite_id: forall x, avoir x -> egale x (op x id);
      gauche_inv: forall x, avoir x -> egale id (op (inv x) x);
      droite_inv: forall x, avoir x -> egale id (op x (inv x))
    }.
    Structure taper := Paquet { sorte; _: @classe_de sorte }.
    Definition classe (cT: taper) :=
      match cT return @classe_de (sorte cT) with
      | Paquet _ c => c
      end.
    Definition supp (cT: taper) := avoir (classe cT).
  End ClasseDef.
  Module Exports.
    Notation groupeTaper := taper.
    Coercion sorte: taper >-> Sortclass.
    Coercion supp: taper >-> Ensemble.
    Definition avoir G := avoir (classe G).
    Definition opg {G} := op (classe G).
    Definition invg {G} := inv (classe G).
    Definition idg {G} := id (classe G).
  End Exports.
End Groupe.
Import Groupe.Exports.
Section GroupeTheorie.
  Context {G:groupeTaper}.
  Definition ferm_op := 
    match G return forall x y, avoir G x -> avoir _ y -> avoir _ (opg x y) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ fop _ _ _ _ _ _) => fop end.
  Definition ferm_inv :=
    match G return forall x, avoir G x -> avoir G (invg x) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ finv _ _ _ _ _) => finv end.
  Definition ferm_id :=
    match G return avoir G idg with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ _ fid _ _ _ _) => fid end.
  Definition assoc_op :=
    match G return forall x y z, avoir G x -> avoir G y -> avoir G z ->
      egale (opg x (opg y z)) (opg (opg x y) z) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ _ _ aop _ _ _) => aop end.
  Definition droite_id :=
    match G return forall x, avoir G x -> egale x (opg x idg) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ _ _ _ did _ _) => did end.
  Definition gauche_inv :=
    match G return forall x, avoir G x -> egale idg (opg (invg x) x) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ _ _ _ _ ginv _) => ginv end.
  Definition droite_inv :=
    match G return forall x, avoir G x -> egale idg (opg x (invg x)) with
    Groupe.Paquet _ (Groupe.Classe _ _ _ _ _ _ _ _ _ _ _ dinv) => dinv end.
  Lemma gauche_id: forall x, avoir G x -> egale x (opg idg x).
  Proof.
    intros x Gx.
    apply (egale_trans(y:= opg x idg)).
    -- apply droite_id, Gx.
    -- apply (egale_trans(y:= opg x (opg (invg x) x))).
    ---- apply (egale_ind _ _ (fun w => egale (opg x idg) (opg x w)) (egale_ref _)).
         apply gauche_inv, Gx.
    ---- apply (egale_trans(y:= opg (opg x (invg x)) x)).
    ------ apply assoc_op; try apply ferm_inv; apply Gx.
    ------ apply (egale_ind _ _ (fun w => egale (opg w x) (opg idg x)) (egale_ref _)).
           apply droite_inv, Gx.
  Qed.
End GroupeTheorie.
  Ltac recrire_egale y :=
    apply (egale_trans(y:=y)).
  Ltac app_f_egale f := apply (f_egale f).
  Ltac recrirex_ex x Gx :=
    apply (egale_trans(y := opg idg x)); try apply gauche_id, Gx.
  Ltac recrirex_xe x Gx :=
    apply (egale_trans(y := opg x idg)); try apply droite_id, Gx.
  Ltac recrirex_ginvgx x Gx g Gg :=
    recrirex_ex x Gx; recrire_egale (opg (opg (invg g) g) x);
    try app_f_egale (fun w => opg w x); try apply gauche_inv, Gg;
    recrire_egale (opg (invg g) (opg g x)); try apply egale_sym, assoc_op; try apply ferm_inv; try apply Gg; try apply Gx.
Section GroupeTheorie.
  Context {G:groupeTaper}.
  Lemma gauche_op_inj: forall g x y, avoir G g -> avoir _ x -> avoir _ y ->
    egale (opg g x) (opg g y) -> egale x y.
  Proof.
    intros g x y Gg Gx Gy Egx_gy.
    recrirex_ginvgx x Gx g Gg.
    apply egale_sym.
    recrirex_ginvgx y Gy g Gg.
    apply f_egale, egale_sym, Egx_gy.
  Qed.
  Lemma gauche_transpo: forall g x y, avoir G g -> avoir G x -> avoir G y ->
    egale (opg g x) y -> egale x (opg (invg g) y).
  Proof.
    intros g x y Gg Gx Gy Egx_y.
    recrirex_ginvgx x Gx g Gg.
    apply f_egale, Egx_y.
  Qed.
  Lemma invinv_ident: forall x, avoir G x -> egale x (invg (invg x)).
  Proof.
    intros x Gx.
    apply (gauche_op_inj (invg x)); try apply ferm_inv; try apply ferm_inv; try apply Gx.
    recrire_egale (@idg G). apply egale_sym, gauche_inv, Gx.
    apply droite_inv, ferm_inv, Gx.
  Qed.
  Lemma invop_opinvinv: forall x y, avoir G x -> avoir G y ->
    egale (invg (opg x y)) (opg (invg y) (invg x)).
  Proof.
    intros x y Gx Gy.
    apply gauche_transpo; try apply ferm_inv; try apply ferm_op; try apply Gx; try apply Gy.
    apply egale_sym. recrire_egale (opg (invg x) idg).
    apply droite_id, ferm_inv, Gx.
    apply egale_sym. apply gauche_transpo.
    apply Gx. apply (ferm_op _ _ Gy (ferm_inv _ (ferm_op _ _ Gx Gy))).
    apply ferm_id. recrire_egale (opg (opg x y) (invg (opg x y))).
    apply assoc_op; try apply ferm_inv, ferm_op; try apply Gx; try apply Gy.
    apply egale_sym, droite_inv, ferm_op. apply Gx. apply Gy.
  Qed.
  Lemma id_invid: egale (@idg G) (invg idg).
  Proof.
    apply egale_sym. recrirex_xe (@invg G idg) (@ferm_inv G _ ferm_id).
    apply egale_sym, gauche_transpo; try apply ferm_id.
    apply egale_sym, droite_id, ferm_id.
  Qed.
End GroupeTheorie.
Section Homomorphisme.
  Context {dom codom:groupeTaper} {f: dom -> codom} (Hc: carto dom codom f).
  Definition hom := forall x y, avoir dom x -> avoir _ y -> egale (f (opg x y)) (opg (f x) (f y)).
  Lemma hom_preserve_id: hom -> egale idg (f idg).
  Proof. 
    intros Hhom.
    recrire_egale (opg (invg (f idg)) (f idg)). apply gauche_inv, Hc, ferm_id.
    apply egale_sym, gauche_transpo; try apply Hc, ferm_id.
    recrire_egale (f (opg idg idg)). apply egale_sym, Hhom; apply ferm_id.
    apply egale_sym. app_f_egale f. apply droite_id, ferm_id.
  Qed.
  Lemma hom_preserve_inv: hom -> forall x, avoir dom x -> egale (f (invg x)) (invg (f x)).
  Proof.
    intros Hhom x Hx.
    recrire_egale (opg (invg (f x)) idg).
    -- apply gauche_transpo; try apply Hc; try apply ferm_inv; try apply Hx; try apply ferm_id.
       recrire_egale (f (opg x (invg x))). apply egale_sym, Hhom; try apply ferm_inv; try apply Hx.
       recrire_egale (f idg). apply f_egale, egale_sym, droite_inv, Hx.
       apply egale_sym, hom_preserve_id, Hhom.
    -- apply egale_sym, droite_id, ferm_inv, Hc, Hx.
  Qed.
End Homomorphisme.

Module SousGroupe.
  Section ClasseDef.
    Record classe_de {G:groupeTaper} := Classe {
      savoir: @Ensemble G;
      sous_ensem: sous savoir G;
      sferm_op: forall x y, savoir x -> savoir y -> savoir (opg x y);
      sferm_inv: forall x, savoir x -> savoir (invg x);
      sferm_id: savoir idg
    }.
    Structure taper := Paquet { sorte; _: @classe_de sorte }.
    Context (cT:taper).
    Definition classe := 
      match cT return @classe_de (sorte cT) with Paquet _ c => c end.
    Definition se := sous_ensem classe.
    Definition groupeTaper :=
      Groupe.Paquet _ (Groupe.Classe _ (savoir _) opg invg idg
        (sferm_op _) (sferm_inv _) (sferm_id _)
        (fun x y z Hx Hy Hz => assoc_op x y z (se _ Hx) (se _ Hy) (se _ Hz))
        (fun x Hx => droite_id x (se _ Hx))
        (fun x Hx => gauche_inv x (se _ Hx))
        (fun x Hx => droite_inv x (se _ Hx))).
  End ClasseDef.
  Module Exports.
    Notation sousgroupeTaper := taper.
    Coercion groupeTaper : taper >-> Groupe.taper.
  End Exports.
End SousGroupe.


Section SousGroupe.
  Variable G H: groupeTaper.
  Definition Gtaper := sorteg G.
  Definition Htaper := sorteg H.
  Variable Eghtaper: egale _ Htaper Gtaper.
  Definition i := inc _ _ Eghtaper.
  Definition sousgroupe := homomorphisme H G i.

  Definition sousgroupenormal :=
    forall (g: sorteg G) (h: sorteg H), avoir _ g -> avoir _ h ->
    exists h', et (avoir H h') (egg _ (i h') (opeg _ (opeg _ g (i h)) (invg _ g))).
End SousGroupe.
Section Noyau.
  Variable f: homTaper.
  Definition H := domf f.
  Definition Hens := Groupe.ensembleTaper H.
  Definition G := codomf f.
  Definition hTaper := sorteg H.
  Definition noyauf_avoir := fun (x: hTaper) => et (avoir Hens x) (egg G (idg _) ((carte f) x)).
  Lemma noyauf_sous: forall x, noyauf_avoir x -> avoir _ x.
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
    - apply (egale_trans _ _ _ _
        (fermer_id _)
        (fermer_ope _ _ _ (fermer_id _) (fermer_id _))
        (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    -- apply droite_id. apply fermer_id.
    -- apply (egale_trans _ _ _ _
         (fermer_ope _ _ _ (fermer_id _) (fermer_id _))
         (fermer_ope _ _ _ (fermer_id _) (fermf _ _ Hy1))
         (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    --- apply (eg_mission _ _ _
          (fermer_id _) (fermf _ _ Hy1)
          Hy2
          (fun w => egg _ (opeg _ (idg _) (idg _)) (opeg _ (idg _) w))).
        apply egale_ref. apply fermer_ope. apply fermer_id. apply fermer_id.
    --- apply (egale_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_id _) (fermf _ _ Hy1))
          (fermer_ope _ _ _ (fermf _ _ Hx1) (fermf _ _ Hy1))
          (fermf _ _ (fermer_ope _ _ _ Hx1 Hy1))).
    ---- apply (eg_mission _ _ _
           (fermer_id _) (fermf _ _ Hx1)
           Hx2
           (fun w => egg _ (opeg _ (idg _) ((carte f) y)) (opeg _ w ((carte f) y)))).
          apply egale_ref. apply fermer_ope. apply fermer_id. apply fermf. apply Hy1.
    ---- apply egale_sym. apply fermf. apply fermer_ope. apply Hx1. apply Hy1.
         apply fermer_ope. apply fermf. apply Hx1. apply fermf. apply Hy1.
         apply hom. apply Hx1. apply Hy1.
  Qed.     
  Lemma noyau_fermer_inv: forall x, avoir noyauEnsemble x ->
    avoir noyauEnsemble (invg _ x).
  Proof.
    intros x Hx. case Hx; intros Hx1 Hx2.
    apply conjonction.
    - apply fermer_inv. apply Hx1.
    - apply (egale_trans _ _ _ _
        (fermer_id _)
        (fermer_inv _ _ (fermer_id _))
        (fermf _ _ (fermer_inv _ _ Hx1))).
    -- apply id_invid.
    -- apply (egale_trans _ _ _ _
         (fermer_inv _ _ (fermer_id _))
         (fermer_inv _ _ (fermf _ _ Hx1))
         (fermf _ _ (fermer_inv _ _ Hx1))).
    --- apply (eg_mission _ _ _
          (fermer_id _)
          (fermf _ _ Hx1)
          Hx2
          (fun w => egg _ (invg _ (idg _)) (invg _ w))).
        apply egale_ref. apply fermer_inv. apply fermer_id.
    --- apply egale_sym. apply fermf. apply fermer_inv. apply Hx1.
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
      unfold avoir. unfold Groupe.ensembleTaper. 
      unfold avoir. simpl. apply conjonction.
    -- apply fermer_ope. apply fermer_ope. apply Hg.
       apply Nh. apply fermer_inv. apply Hg.
    -- apply (egale_trans _ _ _ _
         (fermer_id _)
         (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_inv _ _ (fermf _ _ Hg)))
         (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    --- apply droite_inv. apply fermf. apply Hg.
    --- apply (egale_trans _ _ _ _
          (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ---- apply (eg_mission _ _ _
           (fermf _ _ Hg) (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _))
           (droite_id _ _ (fermf _ _ Hg))
           (fun w => egg _ (opeg _ ((carte f) g) (invg _ ((carte f) g))) (opeg _ w (invg _ ((carte f) g))))).
         apply egale_ref. apply fermer_ope. apply fermf. apply Hg. apply fermer_inv.
         apply fermf. apply Hg.
    ---- apply (egale_trans _ _ _ _
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermer_id _)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
          (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ----- case Nh; intros Nh0 Eefh.
          apply (eg_mission _ _ _
                  (fermer_id _) (fermf _ _ Hh)
                  Eefh
                  (fun w => egg _ (opeg _ (opeg _ ((carte f) g) (idg _)) (invg _ ((carte f) g)))
                                  (opeg _ (opeg _ ((carte f) g) w) (invg _ ((carte f) g))))).
          apply egale_ref. apply fermer_ope. apply fermer_ope. apply fermf. apply Hg.
          apply fermer_id. apply fermer_inv. apply fermf. apply Hg.
    ----- apply (egale_trans _ _ _ _
            (fermer_ope _ _ _ (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).                                  
    ------ apply egale_sym. apply fermer_ope. apply fermf. apply fermer_ope.
           apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
           apply fermer_ope. apply fermer_ope. apply fermf. apply Hg.
           apply fermf. apply Hh. apply fermer_inv. apply fermf. apply Hg. 
           apply (eg_mission _ _ _
             (fermf _ _ (fermer_ope _ _ _ Hg Hh)) 
             (fermer_ope _ _ _ (fermf _ _ Hg) (fermf _ _ Hh))
             (hom f _ _ Hg Hh)
             (fun w => egg _ (opeg _ ((carte f) (opeg _ g h)) (invg _ ((carte f) g)))
                             (opeg _ w (invg _ ((carte f) g))))).
           apply egale_ref. apply fermer_ope. apply fermf. apply fermer_ope.
           apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
    ------ apply (egale_trans _ _ _ _
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermer_inv _ _ (fermf _ _ Hg)))
            (fermer_ope _ _ _ (fermf _ _ (fermer_ope _ _ _ Hg Hh)) (fermf _ _ (fermer_inv _ _ Hg)))
            (fermf _ _ (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)))).
    ------- apply egale_sym. apply fermer_ope. apply fermf. apply fermer_ope.
            apply Hg. apply Hh. apply fermf. apply fermer_inv. apply Hg.
            apply fermer_ope. apply fermf. apply fermer_ope. apply Hg. apply Hh.
            apply fermer_inv. apply fermf. apply Hg.
            apply (eg_mission _ _ _
              (fermf _ _ (fermer_inv _ _ Hg))
              (fermer_inv _ _ (fermf _ _ Hg))
              (hom_preserve_inv _ _ Hg)
              (fun w => egg _ (opeg _ ((carte f) (opeg _ g h)) w)
                              (opeg _ ((carte f) (opeg _ g h)) (invg _ ((carte f) g))))).      
            apply egale_ref. apply fermer_ope. apply fermf. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply fermf. apply Hg.
    ------- apply egale_sym. apply fermf. apply fermer_ope. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply Hg. apply fermer_ope.
            apply fermf. apply fermer_ope. apply Hg. apply Hh. apply fermf.
            apply fermer_inv. apply Hg. apply hom. apply fermer_ope.
            apply Hg. apply Hh. apply fermer_inv. apply Hg.
    - apply egale_ref. apply (fermer_ope _ _ _ (fermer_ope _ _ _ Hg Hh) (fermer_inv _ _ Hg)).
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
    -- apply (egale_trans _ _ _ _
         (fermer_ope _ _ _ Gx Gy)
         (fermer_ope _ _ _ (fermf _ _ Hx') Gy)
         (fermf _ _ (fermer_ope _ _ _ Hx' Hy'))).
    --- apply (eg_mission _ _ _
          Gx (fermf _ _ Hx') xfx' 
          (fun w => egg _ (opeg _ x y) (opeg _ w y))).
        apply egale_ref. apply (fermer_ope _ _ _ Gx Gy).
    --- apply (egale_trans _ _ _ _
          (fermer_ope _ _ _ (fermf _ _ Hx') Gy)
          (fermer_ope _ _ _ (fermf _ _ Hx') (fermf _ _ Hy'))
          (fermf _ _ (fermer_ope _ _ _ Hx' Hy'))).
    ---- apply (eg_mission _ _ _
           Gy (fermf _ _ Hy') yfy' 
           (fun w => egg _ (opeg _ (phi x') y) (opeg _ (phi x') w))).
         apply egale_ref. apply (fermer_ope _ _ _ (fermf _ _ Hx') Gy).
    ---- apply egale_sym. apply fermf. apply fermer_ope. apply Hx'. 
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
    -- apply (egale_trans _ _ _ _
         (fermer_inv _ _ Gx)
         (fermer_inv _ _ (fermf _ _ Hx'))
         (fermf _ _ (fermer_inv _ _ Hx'))).
    --- apply (eg_mission _ _ _
          Gx (fermf _ _ Hx') xfx'
          (fun w => egg _ (invg _ x) (invg _ w))).
        apply egale_ref. apply (fermer_inv _ _ Gx).
    --- apply egale_sym. apply (fermf _ _ (fermer_inv _ _ Hx')).
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

Module Equivalence.
  Section Defs.
    Variable A: ensembleTaper.
    Definition Ta := sortee A.
    Variable rel: Ta -> Ta -> Prop.
    Variable eqrel_ref: forall a: sortee A, avoir A a -> rel a a.
    Variable eqrel_sym: forall a b: sortee A, 
      avoir A a -> avoir A b -> rel a b -> rel b a.
    Variable eqrel_trans: forall a b c: sortee A,
      avoir A a -> avoir A b -> avoir A c -> 
      rel a b -> rel b c -> rel a c.
    Definition eqclasse_avoir (a: Ta) (_: avoir A a) := fun b => et (avoir A b) (rel a b).
    Lemma eqclasse_sous : forall (a: Ta) (Aa: avoir A a) (b:Ta),
      eqclasse_avoir _ Aa b -> avoir A b.
    Proof. intros. case H0; intros. apply H1. Qed.
    Definition eqclasseEnsemble (a: Ta) (Aa: avoir A a) := produire_sousensemble A 
      (eqclasse_avoir _ Aa) (eqclasse_sous _ Aa).
    Lemma eqclasse_rel_ege : forall (x y:Ta) (Ax: avoir A x) (Ay: avoir A y),
      rel x y -> ege (eqclasseEnsemble _ Ax) (eqclasseEnsemble _ Ay) (egreflexion _ _) .
    Proof.
      intros x y Ax Ay Rxy. 
      apply conjonction; unfold sousensemble; 
      unfold CartographieTheorie.Exports.fermer; 
      simpl; intros z H0; case H0; intros Az C_z;
      apply conjonction.
      - apply Az.
      - apply (eqrel_trans _ _ _ Ay Ax Az). apply eqrel_sym. apply Ax.
        apply Ay. apply Rxy. apply C_z.
      - apply Az.
      - apply (eqrel_trans _ _ _ Ax Ay Az). apply Rxy. apply C_z.
    Qed.
    
    Inductive prodEnsEg : Type :=
      enseg : forall (B:ensembleTaper), egale _ Ta (sortee B) -> prodEnsEg.
    Definition prodee_ens (ee:prodEnsEg) :=
      match ee with enseg e _ => e end.
    Definition prodee_eg (ee:prodEnsEg) :=
      match ee return egale _ Ta (sortee (prodee_ens ee)) with enseg _ e => e end.
    Definition eqclasseEnsemble_avoir (ee:prodEnsEg) :=
      match ee with
      | enseg B EAB => exists (a:Ta), et (avoir A a) (forall (Aa: avoir A a), ege (eqclasseEnsemble _ Aa) B EAB)
      end.
    (* Definition eqclasseEnsemble_eg (ee1 ee2:prodEnsEg) :=
      match ee1, ee2 with
      | enseg B EAB, enseg C EAC => ege B C (egale_trans _ _ _ _ (egsym _ _ _ EAB) EAC) 
      end. *)
    (* Definition eqclasseEnsemble_eg (ee1 ee2:prodEnsEg) :=
      match ee1, ee2 with
      | enseg B EAB, enseg C EAC => ege (prodee_ens ee1) (prodee_ens ee2) (egale_trans _ _ _ _ (egsym _ _ _ EAB) EAC) 
      end. *)
    Definition eqclasseEnsemble_eg (ee1 ee2:prodEnsEg) :=
      ege (prodee_ens ee1) (prodee_ens ee2) (egale_trans _ _ _ _ (egsym _ _ _ (prodee_eg ee1)) (prodee_eg ee2)).
    Lemma eqclasseEnsemble_eg_ref : forall (ee:prodEnsEg),
      eqclasseEnsemble_eg ee ee.
    Proof.
      intros ee. unfold eqclasseEnsemble_eg.
      pose (prodee_eg ee) as Eee.
      Check (egale _ Type Type).
      Check (egsym _ _ _ (egreflexion _ Type)).
      case Eee.
      Check (egsym _ _ _ Eee).
      pose (egale_trans _ _ _ _ (egsym _ _ _ Eee) Eee) as uouo.
      case uouo.
      case Eee. apply ege_ref. unfold ege. unfold EnsembleTheorie.ege.

    Definition eqclasseEnsemble := 
      Ensemble.Classe prodEnsEg eqclasseEnsemble_avoir eqclasseEnsemble_eg


    Inductive eqclasse: Type :=
      | C : eqclasseEnsemble -> eqclasse.
    Definition eqclasse_eg (Cx Cy: eqclasse) :=
      match Cx, Cy with
      | C x _, C y _ => rel x y
      end.
    
    (* Variable a b: Ta.
    Variables Aa: avoir A a.
    Variable Ab: avoir A b.
    Definition Ca := C a Aa.
    Definition Cb := C _ Ab.
    Compute (eqclasse_eg Ca Cb). *)
    
  Section ClasseDef.
    Record classe_de (A: ensembleTaper) := Classe {
      rel: sortee A -> sortee A -> Prop;
      equiv_ref: forall a: sortee A, avoir A a -> rel a a;
      equiv_sym: forall a b: sortee A, 
        avoir A a -> avoir A b -> rel a b -> rel b a;
      equiv_trans: forall a b c: sortee A,
        avoir A a -> avoir A b -> avoir A c -> 
        rel a b -> rel b c -> rel a c
    }.
    Structure taper := Paquet { pos; _: classe_de pos }.
    Variable cT: taper.
    Definition classe :=
      match cT return classe_de (pos cT) with
      | Paquet _ c => c
      end.
  End ClasseDef.
  Module Exports.
    Notation




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

