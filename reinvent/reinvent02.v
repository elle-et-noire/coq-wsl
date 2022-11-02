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
  Definition mereEnsemble : Ensemble := fun _ => Vraie.
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
  Definition image : Ensemble := fun y => remplie (fun x => et (A x) (egale y (f x))).
  Definition iminv : Ensemble := fun x => B (f x).
  Definition carto := forall x, A x -> B (f x).
End Cartographie.
Section Cartographie.
  Context {T1 T2:Type} {A:@Ensemble T1} {B:@Ensemble T2} {f: T1 -> T2}.
  Definition inject (Hf: carto A B f) :=
    forall x1 x2, egale (f x1) (f x2) -> egale x1 x2.
  Definition surject (Hf: carto A B f) :=
    forall y, B y -> remplie (fun x => egale y (f x)).
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
Module GroupeTactics.
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
  Ltac recrirex_xgginv x Gx g Gg :=
    recrirex_xe x Gx; recrire_egale (opg x (opg g (invg g)));
    try app_f_egale (opg x); try apply droite_inv, Gg;
    recrire_egale (opg (opg x g) (invg g)); try apply assoc_op; try apply ferm_inv; try apply Gg; try apply Gx.
End GroupeTactics.
Import GroupeTactics.
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
  Lemma droite_transpo: forall g x y, avoir G g -> avoir G x -> avoir G y ->
    egale (opg x g) y -> egale x (opg y (invg g)).
  Proof.
    intros g x y Gg Gx Gy Egx_y.
    recrirex_xgginv x Gx g Gg.
    app_f_egale (fun w => opg w (invg g)). apply Egx_y.
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
Module Homomorphisme.
  Section ClasseDef.
    Record classe_de {dom codom:groupeTaper} {f: dom -> codom} := Classe {
      carto: carto dom codom f;
      hom: forall x y, avoir dom x -> avoir _ y -> egale (f (opg x y)) (opg (f x) (f y))
    }.
    Structure taper := Paquet { dom; codom; f; _: @classe_de dom codom f }.
    Definition classe (cT:taper) :=
      match cT return @classe_de (dom cT) (codom cT) (f cT) with
      Paquet _ _ _ c => c end.
  End ClasseDef.
  Module Exports.
    Notation homTaper := taper.
    Definition dom {cT:taper} := dom cT.
    Definition codom {cT:taper} := codom cT.
    Definition fonc {cT:taper} := f cT.
    Definition carto {cT:taper} := carto (classe cT).
    Definition hom {cT:taper} := hom (classe cT).
  End Exports.
End Homomorphisme.
Import Homomorphisme.Exports.
Section HomomorphismeTheorie.
  Context {phi:homTaper} (f := @fonc phi).
  Lemma hom_preserve_id: egale idg (f idg).
  Proof. 
    recrire_egale (opg (invg (f idg)) (f idg)). apply gauche_inv, carto, ferm_id.
    apply egale_sym, gauche_transpo; try apply carto, ferm_id.
    recrire_egale (f (opg idg idg)). apply egale_sym, hom; apply ferm_id.
    apply egale_sym. app_f_egale f. apply droite_id, ferm_id.
  Qed.
  Lemma hom_preserve_inv: forall x, avoir dom x -> egale (f (invg x)) (invg (f x)).
  Proof.
    intros x Hx.
    recrire_egale (opg (invg (f x)) idg).
    -- apply gauche_transpo; try apply carto; try apply ferm_inv; try apply Hx; try apply ferm_id.
       recrire_egale (f (opg x (invg x))). apply egale_sym, hom; try apply ferm_inv; try apply Hx.
       recrire_egale (f idg). apply f_egale, egale_sym, droite_inv, Hx.
       apply egale_sym, hom_preserve_id.
    -- apply egale_sym, droite_id, ferm_inv, carto, Hx.
  Qed.
End HomomorphismeTheorie.
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
    Definition mereg (H:taper) := sorte H.
  End Exports.
End SousGroupe.
Import SousGroupe.Exports.
Section SousGroupeTheorie.
  Context (H:sousgroupeTaper).
  Definition sousg_sousens := 
    match H return sous H (mereg H) with
    SousGroupe.Paquet _ (SousGroupe.Classe _ _ se _ _ _) => se end.
  Definition sousgnormal := forall h, avoir H h ->
   forall (g: mereg H), avoir _ g -> avoir H (opg (opg g h) (invg g)).
End SousGroupeTheorie.
Section Homomorphisme.
  Context {ht:homTaper} (f := @fonc ht) (imf := image dom f).
  Definition image_sous : sous imf codom := fun y Imy =>
    match Imy with exiter _ x Px => 
      match Px with conjonction _ _ Hx Eyfx =>
        egale_ind _ _ (avoir codom) (carto x Hx) _ (egale_sym Eyfx) end end.
  Lemma image_sferm_op : forall x y, imf x -> imf y -> imf (opg x y).
  Proof. 
    intros x y Imx Imy. destruct Imx as [x' [Hx' Exfx']]. destruct Imy as [y' [Hy' Eyfy']].
    apply (exiter _ (opg x' y')), conjonction.
    -- apply ferm_op. apply Hx'. apply Hy'.
    -- recrire_egale (opg x (f y')). apply f_egale, Eyfy'.
       recrire_egale (opg (f x') (f y')).
       app_f_egale (fun w => opg w (f y')). apply Exfx'.
       apply egale_sym, hom. apply Hx'. apply Hy'.
  Qed.
  Lemma image_sferm_inv : forall x, imf x -> imf (invg x).
  Proof.
    intros x Imx. destruct Imx as [x' [Hx' Exfx']]. 
    apply (exiter _ (invg x')), conjonction.
    -- apply ferm_inv, Hx'.
    -- recrire_egale (invg (f x')). apply f_egale, Exfx'.
       apply egale_sym, hom_preserve_inv, Hx'.
  Qed.
  Lemma image_sferm_id : imf idg.
  Proof. apply (exiter _ idg); apply conjonction. apply ferm_id. apply hom_preserve_id. Qed.
  Definition imageSG := SousGroupe.Paquet codom (SousGroupe.Classe codom imf image_sous
    image_sferm_op image_sferm_inv image_sferm_id).

  Definition noyau : Ensemble := fun x => et (avoir dom x) (egale idg (f x)).
  Lemma noyau_sous : sous noyau dom.
  Proof. intros x Nx; apply (et_prj1 Nx). Qed.
  Lemma noyau_sferm_op : forall x y, noyau x -> noyau y -> noyau (opg x y).
  Proof.
    intros x y Nx Ny; destruct Nx as [Nx Eefx]; destruct Ny as [Ny Eefy]; apply conjonction.
    -- apply ferm_op. apply Nx. apply Ny.
    -- recrire_egale (@opg (@codom ht) idg idg).
       apply droite_id, ferm_id. recrire_egale (opg idg (f y)).
       apply f_egale, Eefy. recrire_egale (opg (f x) (f y)).
       app_f_egale (fun w => opg w (f y)). apply Eefx.
       apply egale_sym, hom. apply Nx. apply Ny.
  Qed.
  Lemma noyau_sferm_inv : forall x, noyau x -> noyau (invg x).
  Proof.
    intros x Nx; destruct Nx as [Nx Eefx]; apply conjonction.
    -- apply ferm_inv, Nx.
    -- recrire_egale (@invg (@codom ht) idg). apply id_invid.
       recrire_egale (invg (f x)). apply f_egale, Eefx.
       apply egale_sym, hom_preserve_inv, Nx.
  Qed.
  Lemma noyau_sferm_id : noyau idg.
  Proof. apply conjonction. apply ferm_id. apply hom_preserve_id. Qed.
  Definition noyauSG := SousGroupe.Paquet dom (SousGroupe.Classe dom noyau noyau_sous
  noyau_sferm_op noyau_sferm_inv noyau_sferm_id).
  Lemma noyauSG_normal : sousgnormal noyauSG.
  Proof.
    intros h Hh g Gg; destruct Hh as [Nh Eefh]; apply conjonction.
    -- apply ferm_op. apply ferm_op. apply Gg. apply Nh. 
       apply ferm_inv. apply Gg.
    -- recrire_egale (opg (f g) (invg (f g))). apply droite_inv, carto, Gg.
       recrire_egale (opg (f (opg g h)) (invg (f g))).
       assert (egale (f g) (f (opg g h))) as Efg_fgh.
       { recrire_egale (opg (f g) idg). apply droite_id, carto, Gg.
         recrire_egale (opg (f g) (f h)). apply f_egale, Eefh.
         apply egale_sym, hom. apply Gg. apply Nh. }
       app_f_egale (fun w => opg w (invg (f g))). apply Efg_fgh.
       recrire_egale (opg (f (opg g h)) (f (invg g))).
       apply f_egale, egale_sym, hom_preserve_inv, Gg.
       apply egale_sym, hom. apply ferm_op. apply Gg. apply Nh.
       apply ferm_inv, Gg.
  Qed.
End Homomorphisme.
Module Reldeq.
  Section ClasseDef.
    Record classe_de {T} {A: @Ensemble T} := Classe {
      rel: T -> T -> Prop;
      rel_ref: forall a, A a -> rel a a;
      rel_sym: forall a b, A a -> A b -> rel a b -> rel b a;
      rel_trans: forall a b c, A a -> A b -> A c ->
        rel a b -> rel b c -> rel a c
    }.
    Structure taper := Paquet { sorte; supp; _: @classe_de sorte supp }.
    Definition classe (cT:taper) :=
      match cT return @classe_de (sorte cT) (supp cT) with Paquet _ _ c => c end.
  End ClasseDef.
  Module Exports.
    Notation reldeqTaper := taper.
    Coercion supp : taper >-> Ensemble.
    Coercion sorte: taper >-> Sortclass.
    Definition rel {cT:taper} := rel (classe cT).
    Definition supp := supp.
  End Exports.
End Reldeq.
Import Reldeq.Exports.
Section ReldeqTheorie.
  Context {re:reldeqTaper}.
  Definition rel_ref :=
    match re return forall a, supp re a -> rel a a with
    Reldeq.Paquet _ _ (Reldeq.Classe _ _ _ ref' _ _) => ref' end.
  Definition rel_sym :=
    match re return forall a b, supp re a -> supp re b -> rel a b -> rel b a with
    Reldeq.Paquet _ _ (Reldeq.Classe _ _ _ _ sym' _) => sym' end.
  Definition rel_trans :=
    match re return forall a b c, supp re a -> supp re b -> supp re c ->
        rel a b -> rel b c -> rel a c with
    Reldeq.Paquet _ _ (Reldeq.Classe _ _ _ _ _ trans') => trans' end.
  Definition classedeq_de x : Ensemble := fun y => et (supp re y) (rel x y).
  Lemma classedeq_avoir_ref : forall x, supp re x -> (classedeq_de x) x.
  Proof. intros x Rx. apply conjonction. apply Rx. apply rel_ref, Rx. Qed.
  Lemma ssi_rel_egcdeq : forall x y, supp re x -> supp re y ->
    ssi (rel x y) (egale (classedeq_de x) (classedeq_de y)).
  Proof.
    intros x y Rx Ry. apply conjonction.
    -- intros Rxy. apply egale_ens, conjonction.
    ---- intros z [Rz Rxz]. apply conjonction. apply Rz. apply (rel_trans y x z Ry Rx Rz (rel_sym _ _ Rx Ry Rxy) Rxz).
    ---- intros z [Rz Ryz]. apply conjonction. apply Rz. apply (rel_trans x y z Rx Ry Rz Rxy Ryz).
    -- intros ECxCy. apply rel_sym. apply Ry. apply Rx.
       apply (et_prj2 (egale_ind _ (classedeq_de x) (fun C => C x) (classedeq_avoir_ref x Rx) (classedeq_de y) ECxCy)).
  Qed.
  Lemma cdeqoverlap_rel : forall x y, supp re x -> supp re y -> 
    remplie (intsec (classedeq_de x) (classedeq_de y)) -> rel x y.
  Proof.
    intros x y Rx Ry [z [Cxz Cyz]]. apply (rel_trans x z y).
    apply Rx. apply (et_prj1 Cxz). apply Ry.
    apply (et_prj2 Cxz). apply rel_sym. apply Ry. apply (et_prj1 Cyz). apply (et_prj2 Cyz).
  Qed.
  Definition classedeqEnsemble : @Ensemble (@Ensemble re) :=
    fun Cx => remplie (fun y => et (supp re y) (egale (classedeq_de y) Cx)).
  Lemma classedeqEns_avoir_claassedeq : forall x, supp re x -> classedeqEnsemble (classedeq_de x).
  Proof. intros x Rx. apply (exiter _ x). apply conjonction. apply Rx. apply egale_ref. Qed.
End ReldeqTheorie.
Section Coset.
  Context (H:sousgroupeTaper).
  Definition cosetGaucheRel g g' := remplie (fun h => et (avoir H h) (egale g (@opg (mereg H) g' h))).
  Definition cosetDroiteRel g g' := remplie (fun h => et (avoir H h) (egale g (@opg (mereg H) h g'))).
  Lemma cosetGRel_ref : forall g, avoir (mereg H) g -> cosetGaucheRel g g.
  Proof. 
    intros g Gg. apply (exiter _ (@idg H)), conjonction. apply ferm_id.
    recrire_egale (opg g (@idg (mereg H))). apply droite_id, Gg. apply f_egale, egale_ref.
  Qed.
  Lemma cosetGRel_sym: forall g g', avoir (mereg H) g -> avoir (mereg H) g' ->
    cosetGaucheRel g g' -> cosetGaucheRel g' g.
  Proof.
    intros g g' Gg Gg' [h [Hh Eg_g'h]]. apply (exiter _ (@invg H h)), conjonction.
    -- apply ferm_inv, Hh.
    -- recrire_egale (opg g (@invg (mereg H) h)). apply droite_transpo. apply sousg_sousens, Hh.
       apply Gg'. apply Gg. apply egale_sym, Eg_g'h. apply egale_ref.
  Qed.
  Lemma cosetGRel_trans: forall g1 g2 g3, avoir (mereg H) g1 -> avoir (mereg H) g2 -> avoir (mereg H) g3 ->
    cosetGaucheRel g1 g2 -> cosetGaucheRel g2 g3 -> cosetGaucheRel g1 g3.
  Proof.
    intros g1 g2 g3 Gg1 Gg2 Gg3 [h12 [Hh12 Rg1g2]] [h23 [Hh23 Rg2g3]].
    apply (exiter _ (@opg H h23 h12)), conjonction.
    -- apply ferm_op. apply Hh23. apply Hh12.
    -- recrire_egale (opg g2 h12). apply Rg1g2. recrire_egale (opg (@opg (mereg H) g3 h23) h12).
       app_f_egale (fun w => opg w h12). apply Rg2g3.
       apply egale_sym. recrire_egale (opg g3 (@opg (mereg H) h23 h12)).
       apply egale_ref. apply assoc_op. apply Gg3. apply sousg_sousens, Hh23. apply sousg_sousens, Hh12.
  Qed.
  Definition cosetGaucheReldeq := Reldeq.Paquet _ (mereg H) (Reldeq.Classe _ _ cosetGaucheRel
    cosetGRel_ref cosetGRel_sym cosetGRel_trans).
  Definition cosetGaucheEnsemble := @classedeqEnsemble cosetGaucheReldeq.

  Lemma cosetDRel_ref : forall g, avoir (mereg H) g -> cosetDroiteRel g g.
  Proof. 
    intros g Gg. apply (exiter _ (@idg H)), conjonction. apply ferm_id.
    recrire_egale (opg (@idg (mereg H)) g). apply gauche_id, Gg. apply f_egale, egale_ref.
  Qed.
  Lemma cosetDRel_sym: forall g g', avoir (mereg H) g -> avoir (mereg H) g' ->
    cosetDroiteRel g g' -> cosetDroiteRel g' g.
  Proof.
    intros g g' Gg Gg' [h [Hh Eg_hg']]. apply (exiter _ (@invg H h)), conjonction.
    -- apply ferm_inv, Hh.
    -- recrire_egale (opg (@invg (mereg H) h) g). apply gauche_transpo. apply sousg_sousens, Hh.
       apply Gg'. apply Gg. apply egale_sym, Eg_hg'. apply egale_ref.
  Qed.
  Lemma cosetDRel_trans: forall g1 g2 g3, avoir (mereg H) g1 -> avoir (mereg H) g2 -> avoir (mereg H) g3 ->
    cosetDroiteRel g1 g2 -> cosetDroiteRel g2 g3 -> cosetDroiteRel g1 g3.
  Proof.
    intros g1 g2 g3 Gg1 Gg2 Gg3 [h12 [Hh12 Rg1g2]] [h23 [Hh23 Rg2g3]].
    apply (exiter _ (@opg H h12 h23)), conjonction.
    -- apply ferm_op. apply Hh12. apply Hh23.
    -- recrire_egale (opg h12 g2). apply Rg1g2. recrire_egale (@opg (mereg H) h12 (@opg (mereg H) h23 g3)).
       apply f_egale, Rg2g3. apply egale_sym.
      recrire_egale (opg (@opg (mereg H) h12 h23) g3).
       apply egale_ref. apply egale_sym, assoc_op. apply sousg_sousens, Hh12. apply sousg_sousens, Hh23. apply Gg3.
  Qed.
  Definition cosetDroiteReldeq := Reldeq.Paquet _ (mereg H) (Reldeq.Classe _ _ cosetDroiteRel
    cosetDRel_ref cosetDRel_sym cosetDRel_trans).
  Definition cosetDroiteEnsemble := @classedeqEnsemble cosetDroiteReldeq.
  
  Context (H_normal: sousgnormal H).
  Lemma sgnormal_gd_egale : forall g, avoir (mereg H) g -> forall h, avoir H h -> remplie (fun h' => et (avoir H h') (egale (@opg (mereg H) g h) (opg h' g))).
  Proof.
    intros g Gg h Hh. apply (exiter _ (opg (opg g h) (invg g))), conjonction.
    -- apply H_normal. apply Hh. apply Gg.
    -- assert (forall x, avoir (mereg H) x -> egale x (opg (opg x (invg g)) g)) as Ex_xxinvgg.
       { intros x Gx. recrire_egale (opg x idg). apply droite_id, Gx. 
         recrire_egale (opg x (opg (invg g) g)). apply f_egale, gauche_inv, Gg.
         apply assoc_op. apply Gx. apply ferm_inv, Gg. apply Gg. }
       apply Ex_xxinvgg, ferm_op. apply Gg. apply sousg_sousens, Hh.
  Qed.
  Lemma sgnormal_dg_egale : forall g, avoir (mereg H) g -> forall h, avoir H h -> remplie (fun h' => et (avoir H h') (egale (@opg (mereg H) h g) (opg g h'))).
  Proof.
    intros g Gg h Hh. apply (exiter _ (opg (opg (invg g) h) g)), conjonction.
    -- apply (fun Hw => egale_ind _ (invg (invg g)) (fun w => avoir H (opg (opg (invg g) h) w)) Hw). apply H_normal.
       apply Hh. apply ferm_inv, Gg. apply egale_sym, invinv_ident, Gg.
    -- assert (forall x, avoir (mereg H) x -> egale x (opg g (opg (invg g) x))) as Ex_ginvgx.
       { intros x Gx. recrire_egale (opg idg x). apply gauche_id, Gx. 
         recrire_egale (opg (opg g (invg g)) x). app_f_egale (fun w => opg w x). apply droite_inv, Gg.
         apply egale_sym, assoc_op. apply Gg. apply ferm_inv, Gg. apply Gx. }
       recrire_egale (opg g (opg (invg g) (opg h g))).
       apply Ex_ginvgx. apply (fun Hw => egale_ind _ (@opg (mereg H) h g) (fun w => avoir (mereg H) w) Hw).
       apply ferm_op. apply sousg_sousens, Hh. apply Gg. apply egale_ref.
       apply f_egale. recrire_egale (opg (invg g) (@opg (mereg H) h g)).
       apply egale_ref. apply assoc_op. apply ferm_inv, Gg. apply sousg_sousens, Hh. apply Gg.
  Qed.
  Lemma cosetdesgnormal_classedegd_egale : forall g, avoir (mereg H) g ->
    egale (@classedeq_de cosetGaucheReldeq g) (@classedeq_de cosetDroiteReldeq g).
  Proof.
    intros g Gg. apply egale_ens, conjonction.
    -- intros g' [Gg' [h [Hh Eg_g'h]]]. apply conjonction. apply Gg'.
       apply (exiter _ (opg (opg g' h) (invg g'))), conjonction.
    ---- apply H_normal. apply Hh. apply Gg'.
    ---- recrire_egale (opg g' h). apply Eg_g'h.
         assert (forall x, avoir (mereg H) x -> egale x (opg (opg x (invg g')) g')) as Ex_xxinvgg.
         { intros x Gx. recrire_egale (opg x idg). apply droite_id, Gx. 
           recrire_egale (opg x (opg (invg g') g')). apply f_egale, gauche_inv, Gg'.
           apply assoc_op. apply Gx. apply ferm_inv, Gg'. apply Gg'. }
         apply Ex_xxinvgg. apply ferm_op. apply Gg'. apply sousg_sousens, Hh.
    -- intros g' [Gg' [h [Hh Eg_hg']]]. apply conjonction. apply Gg'.
       apply (exiter _ (opg (opg (invg g') h) g')), conjonction.
    ---- apply (egale_ind _ (invg (invg g')) (fun w => avoir H (opg (opg (invg g') h) w))).
         apply H_normal. apply Hh. apply ferm_inv, Gg'. apply egale_sym, invinv_ident, Gg'.
    ---- recrire_egale (@opg (mereg H) h g'). apply Eg_hg'.
         apply egale_sym. recrire_egale (opg g' (opg (invg g') (@opg (mereg H) h g'))).
         apply f_egale, egale_sym, assoc_op. apply ferm_inv, Gg'. apply sousg_sousens, Hh. apply Gg'.
         recrire_egale (opg (opg g' (invg g')) (@opg (mereg H) h g')).
         apply assoc_op. apply Gg'. apply ferm_inv, Gg'. apply ferm_op. apply sousg_sousens, Hh. apply Gg'.
         recrire_egale (opg (@idg (mereg H)) (@opg (mereg H) h g')). app_f_egale (fun w => opg w (@opg (mereg H) h g')).
         apply egale_sym, droite_inv, Gg'.
         apply egale_sym, gauche_id, ferm_op. apply sousg_sousens, Hh. apply Gg'.
  Qed.
  Lemma cosetdesgnormal_quotdegd_egale : egale cosetGaucheEnsemble cosetDroiteEnsemble.
  Proof. 
    apply egale_ens, conjonction; intros Cg [g [Gg ECgCg]]; apply (exiter _ g), conjonction; try apply Gg. 
    recrire_egale (@classedeq_de cosetGaucheReldeq g). apply egale_sym, cosetdesgnormal_classedegd_egale, Gg. apply ECgCg.
    recrire_egale (@classedeq_de cosetDroiteReldeq g). apply cosetdesgnormal_classedegd_egale, Gg; apply ECgCg. apply ECgCg.
  Qed.
  Definition cosetop (g1H g2H: @Ensemble (mereg H)) : Ensemble := 
    fun g => remplie (fun g1' => et (g1H g1') (remplie 
      (fun g2' => et (g2H g2') (egale (@opg (mereg H) g1' g2') g)))).
  (* avoir H (opg g1' g) と g1H g1' から avoir G g を復元できない assoc_op を使うには G g が必要なので。 *)
  Definition cosetinv (g1H: @Ensemble (mereg H)) : Ensemble :=
    fun g => et (avoir (mereg H) g) (remplie (fun g1' => et (g1H g1') (avoir H (opg g1' g)))).
  Definition cosetid := @classedeq_de cosetGaucheReldeq (@idg (mereg H)).
  Lemma coset_ferm_op : forall g1H g2H, cosetGaucheEnsemble g1H ->
    cosetGaucheEnsemble g2H -> cosetGaucheEnsemble (cosetop g1H g2H).
  Proof.
    intros g1H g2H [g1' [Gg1' Eg1'H_g1H]] [g2' [Gg2' Eg2'H_g2H]]. 
    apply (exiter _ (opg g1' g2')), conjonction.
    -- apply ferm_op. apply Gg1'. apply Gg2'.
    -- apply egale_ens, conjonction.
    ---- intros g [Gg [h [Hh Eg1'g2'_gh]]]. apply (exiter _ g1'), conjonction.
         apply (egale_ind _ _ (fun w => w g1') (classedeq_avoir_ref _ Gg1') _ Eg1'H_g1H).
         apply (exiter _ (opg g2' (@invg H h))), conjonction.
         apply (fun Hw => (egale_ind _ _ (fun w => w (opg g2' (invg h))) Hw _ Eg2'H_g2H)).
         apply conjonction. apply ferm_op. apply Gg2'.
         apply (fun Hw => egale_ind _ (@invg (mereg H) h) (@avoir (mereg H)) Hw _ (egale_ref _)). 
         apply ferm_inv, sousg_sousens, Hh. apply (exiter _ h), conjonction.
         apply Hh. recrire_egale (opg g2' idg). apply droite_id, Gg2'.
         recrire_egale (opg g2' (opg (invg h) h)). apply f_egale.
         recrire_egale (@idg H). apply egale_ref. apply gauche_inv, Hh.
         recrire_egale (opg g2' (@opg (mereg H) (invg h) h)).
         apply egale_ref. apply assoc_op. apply Gg2'. apply sousg_sousens, ferm_inv, Hh.
         apply sousg_sousens, Hh. recrire_egale (opg (opg g1' g2') (@invg (mereg H) h)).
         apply assoc_op. apply Gg1'. apply Gg2'. apply ferm_inv, sousg_sousens, Hh.
         apply egale_sym, droite_transpo. apply sousg_sousens, Hh. apply Gg.
         apply ferm_op. apply Gg1'. apply Gg2'. apply egale_sym, Eg1'g2'_gh.
    ---- intros g [g1'' [g1Hg1'' [g2'' [g2Hg2'' Eg1''g2''_g]]]].
         destruct (egale_ind _ _ (fun w => w g1'') g1Hg1'' _ (egale_sym Eg1'H_g1H)) as [Gg1'' [h1 [Hh1 Eg1'_g1''h1]]].
         destruct (egale_ind _ _ (fun w => w g2'') g2Hg2'' _ (egale_sym Eg2'H_g2H)) as [Gg2'' [h2 [Hh2 Eg2'_g2''h2]]].
         destruct (sgnormal_dg_egale g2' Gg2' _ Hh1) as [h2' [Hh2' Einvh1g2'_g2'h2']].
         apply conjonction. case Eg1''g2''_g. apply ferm_op. apply Gg1''. apply Gg2''.
         apply (exiter _ (opg h2 h2')), conjonction.
         apply ferm_op. apply Hh2. apply Hh2'.
         case Eg1''g2''_g. recrire_egale (opg (opg g1'' (opg g2'' h2)) h2').
         case Eg2'_g2''h2. recrire_egale (opg g1'' (opg g2' h2')).
         case Einvh1g2'_g2'h2'. recrire_egale (opg (opg g1'' h1) g2').
         case Eg1'_g1''h1. apply egale_ref. apply egale_sym, assoc_op.
         apply Gg1''. apply sousg_sousens, Hh1. apply Gg2'.
         apply assoc_op. apply Gg1''. apply Gg2'. apply sousg_sousens, Hh2'.
         recrire_egale (opg (opg (opg g1'' g2'') h2) h2').
         app_f_egale (fun w => opg w h2'). recrire_egale (opg g1'' (@opg (mereg H) g2'' h2)).
         apply egale_ref. apply assoc_op. apply Gg1''. apply Gg2''. apply sousg_sousens, Hh2.
         apply egale_sym. recrire_egale (opg (opg g1'' g2'') (@opg (mereg H) h2 h2')).
         apply egale_ref. apply assoc_op. apply ferm_op. apply Gg1''. apply Gg2''.
         apply sousg_sousens, Hh2. apply sousg_sousens, Hh2'.
  Qed.
  Lemma cosetid_H : egale cosetid H.
  Proof. 
    apply egale_ens, conjonction; intros h. 
     -- intros [Gh [h' [Hh' Ee_hh']]]. 
        assert (egale h (opg idg (@invg H h'))) as Eh_einvgh'.
        { recrire_egale (opg idg (@invg (mereg H) h')).
          apply droite_transpo. apply sousg_sousens, Hh'. 
          apply Gh. apply ferm_id. apply egale_sym, Ee_hh'.
          apply egale_ref. }
        apply (fun Hw => egale_ind _ _ (fun w => avoir H w) Hw _ (egale_sym Eh_einvgh')).
        apply ferm_op. apply ferm_id. apply ferm_inv, Hh'.
     -- intros Hh. apply conjonction. apply sousg_sousens, Hh.
        apply (exiter _ (@invg H h)), conjonction. apply ferm_inv, Hh.
        recrire_egale (@idg H). apply egale_ref. recrire_egale (@opg H h (@invg H h)). apply droite_inv, Hh.
        apply egale_ref.
  Qed.
  Lemma coset_ferm_inv : forall g1H, 
    cosetGaucheEnsemble g1H -> cosetGaucheEnsemble (cosetinv g1H).
  Proof.
    intros g1H [g1' [Gg1' Eg1'Hg1H]]. apply (exiter _ (invg g1')), conjonction.
     -- apply ferm_inv, Gg1'.
     -- case Eg1'Hg1H. apply egale_ens, conjonction.
     ---- intros g [Gg [h [Hh Einvg1'_gh]]]. apply conjonction. apply Gg. apply (exiter _ (invg g)), conjonction.
     ------ apply conjonction. apply ferm_inv, Gg. 
            destruct (sgnormal_dg_egale _ (ferm_inv _ Gg) (invg h) (ferm_inv _ Hh)) as [h' [Hh' Eihig_igh']].
            apply (exiter _ h'), conjonction. apply Hh'. case Eihig_igh'.
            recrire_egale (invg (opg g h)). case Einvg1'_gh. apply invinv_ident, Gg1'.
            recrire_egale (opg (@invg (mereg H) h) (invg g)). apply invop_opinvinv.
            apply Gg. apply sousg_sousens, Hh. apply egale_ref.
     ------ apply (egale_ind _ _ (avoir H) ferm_id _ (gauche_inv _ Gg)).
     ---- intros g [Gg [g' [[Gg' [h [Hh Eg1'_g'h]]] Hg'g]]]. apply conjonction. 
          apply Gg. destruct (sgnormal_dg_egale _ Gg _ (ferm_inv _ Hh)) as [h' [Hh' Eihg_gh']].
          apply (exiter _ (opg h' (@invg H (opg g' g)))), conjonction.
          apply ferm_op. apply Hh'. apply ferm_inv, Hg'g.
          recrire_egale (opg (opg g h') (invg (opg g' g))).
          case Eihg_gh'. recrire_egale (opg (opg (invg h) g) (opg (invg g) (invg g'))).
          recrire_egale (opg (invg h) (invg g')). recrire_egale (invg (opg g' h)).
          apply f_egale, Eg1'_g'h. recrire_egale (opg (@invg (mereg H) h) (invg g')).
          apply invop_opinvinv. apply Gg'. apply sousg_sousens, Hh. apply egale_ref.
          recrire_egale (opg (opg (@invg (mereg H) h) idg) (invg g')). 
          app_f_egale (fun w => opg w (invg g')). apply droite_id.
          apply ferm_inv, sousg_sousens, Hh.
          recrire_egale (opg (opg (invg h) (opg g (invg g))) (invg g')).
          app_f_egale (fun w => opg (opg (invg h) w) (invg g')). recrire_egale (@idg (mereg H)).
          apply egale_ref. apply droite_inv, Gg.
          recrire_egale (opg (opg (opg (invg h) g) (invg g)) (invg g')).
          app_f_egale (fun w => opg w (invg g')). recrire_egale (opg (@invg (mereg H) h) (opg g (invg g))).
          apply egale_ref. recrire_egale (opg (opg (@invg (mereg H) h) g) (invg g)). apply assoc_op.
          apply ferm_inv, sousg_sousens, Hh. apply Gg. apply ferm_inv, Gg.
          apply egale_ref. apply egale_sym. recrire_egale (opg (opg (@invg (mereg H) h) g) (opg (invg g) (invg g'))).
          apply egale_ref. recrire_egale (opg (opg (opg (@invg (mereg H) h) g) (invg g)) (invg g')).
          apply assoc_op. apply ferm_op. apply ferm_inv, sousg_sousens, Hh.
          apply Gg. apply ferm_inv, Gg. apply ferm_inv, Gg'.
          apply egale_ref. apply f_egale. apply egale_sym.
          recrire_egale (@invg (mereg H) (opg g' g)). apply egale_ref.
          apply invop_opinvinv. apply Gg'. apply Gg.
          apply egale_sym. recrire_egale (opg g (@opg (mereg H) h' (@invg (mereg H) (opg g' g)))).
          apply egale_ref. recrire_egale (opg (opg g h') (@invg (mereg H) (opg g' g))).
          apply assoc_op. apply Gg. apply sousg_sousens, Hh'. apply ferm_inv, sousg_sousens, Hg'g.
          apply egale_ref.
  Qed.
End Coset.
