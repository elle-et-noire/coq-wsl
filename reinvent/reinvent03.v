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
      exister : forall x, P x -> remplie P.
    Context {T:Prop} {P: T -> Prop}.
    Definition ex_prj1 (H: remplie P):=
      match H with exister _ a _ => a end.
    (* This returns independent type, so one has to let H be free. *)
    Definition ex_prj2 (H: remplie P) :=
      match H return P (ex_prj1 H) with exister _ _ Pa => Pa end.
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
      match HP with exister _ x _ => habit _ x end.
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
  Definition ensem : Type := T -> Prop.
  Definition ont (e:ensem) x := e x.
  Inductive pos : Type :=
    etre : forall (e:ensem) x, e x -> pos.
  Definition elem p : T := match p with
    etre _ x _ => x end.
  Coercion elem : pos >-> T.
End Ensemble.
Check elem.
Definition elem' (T:Type) (p:@pos T) := elem p.
Coercion elem' : pos >-> T.
Section uo.
Print Coercions.
Variable T:Type.
Variable p : @pos T.
Variable f: T -> T.
Check f (elem p).
  Definition avoir A := match A return sorte A -> Prop with
    wrap _ e => match e with pos a => a end end.
  Context {T:Type}.
  Definition videens := @pos T (fun _ => Faux).
  Definition mereens := @pos T (fun _ => Vraie).
  Definition seulens (x:T) := pos (egale x).
  Definition syndens (e1 e2:@ensem T) := pos (fun x => ou (ont e1 x) (ont e2 x)).
  Definition complens (e:@ensem T) := pos (fun x => nepas (ont e x)).
  Definition intsecens (e1 e2:@ensem T) := pos (fun x => et (ont e1 x) (ont e2 x)).
  Definition moinsens e1 e2 := intsecens e1 (complens e2).
  Definition sous (e1 e2:@ensem T) := forall x:.
  Inductive sous {P Q: T -> Prop} 

  Axiom egale_cond : forall A B, et (sous A B) (sous B A) -> egale A B.
End Ensemble.

Section gue.
Definition m := fun _:naturelle => Vraie.
Definition gue := pos m.
Definition p : gue -> naturelle := @pos_prj1 _ m.
Coercion p : gue >-> naturelle.
Print Coercions.
Variable uouo: gue.
Check (ajouter uouo uouo).
Check (ajouter (pos_prj1 uouo) (pos_prj1 uouo)).
Check (uouo: naturelle).
End gue.

Section Cartographie.
  Context {A B: Type} (f: A -> B).
  Definition image := pos (fun y => remplie (fun x => egale y (f x))).
  Definition preimage := pos (fun x => remplie (fun y => egale y (f x))).
End Cartographie.
Section Cartographie.
  Context {A B:Type} (f: A -> B).
  Definition inj :=
    forall x1 x2, egale (f x1) (f x2) -> egale x1 x2.
  Definition surj :=
    forall y, remplie (fun x => egale y (f x)).
  Definition bij := et inj surj.
  Definition iminv_g (g: B -> A) := forall a, egale a (g (f a)).
  Definition iminv_d (g: B -> A) := forall b, egale b (f (g b)).
  Definition iminv (g: B -> A) := et (iminv_g g) (iminv_d g).
  Axiom surj_remp_iminv_d : surj -> remplie iminv_d.
  Axiom inj_remp_iminv_g : inj -> remplie iminv_g.
  Axiom bij_remp_iminv : bij -> remplie iminv.
  Lemma remp_iminv_d_surj : remplie iminv_d -> surj.
  Proof. intros [g g_inv] y; apply (exister _ (g y)), g_inv. Qed.
  Lemma remp_iminv_g_inj : remplie iminv_g -> inj.
  Proof. intros [g g_inv] x1 x2 E. case (egale_sym (g_inv x1)), (egale_sym (g_inv x2)). apply f_egale, E. Qed.
  Lemma ssi_bij_carinv : ssi bij (remplie iminv).
  Proof.
    apply conjonction. apply  
     -- intros [Hinj Hsurj]. destruct (surj_remp_iminv_d Hsurj) as [g Hd].
        apply (exister _ g), conjonction.  apply inj_remp_iminv_g, Hinj. apply surj_remp_iminv_d, Hsurj.
    intros [Hg Hd]. apply conjonction. apply remp_iminv_g_inj, Hg. apply remp_iminv_d_surj, Hd.
  Qed.
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
  Ltac rec_egale y :=
    apply (egale_trans(y:=y)).
  Ltac app_f_egale f := apply (f_egale f).
  Ltac rec_x_ex x Gx :=
    apply (egale_trans(y := opg idg x)); try apply gauche_id, Gx.
  Ltac rec_x_xe x Gx :=
    apply (egale_trans(y := opg x idg)); try apply droite_id, Gx.
  Ltac rec_x_gigx x Gx g Gg :=
    rec_x_ex x Gx; rec_egale (opg (opg (invg g) g) x);
    try app_f_egale (fun w => opg w x); try apply gauche_inv, Gg;
    rec_egale (opg (invg g) (opg g x)); try apply egale_sym, assoc_op; try apply ferm_inv; try apply Gg; try apply Gx.
  Ltac rec_x_xgig x Gx g Gg :=
    rec_x_xe x Gx; rec_egale (opg x (opg g (invg g)));
    try app_f_egale (opg x); try apply droite_inv, Gg;
    rec_egale (opg (opg x g) (invg g)); try apply assoc_op; try apply ferm_inv; try apply Gg; try apply Gx.
End GroupeTactics.
Import GroupeTactics.
Section GroupeTheorie.
  Context {G:groupeTaper}.
  Lemma gauche_op_inj: forall g x y, avoir G g -> avoir _ x -> avoir _ y ->
    egale (opg g x) (opg g y) -> egale x y.
  Proof.
    intros g x y Gg Gx Gy Egx_gy.
    rec_x_gigx x Gx g Gg.
    apply egale_sym.
    rec_x_gigx y Gy g Gg.
    apply f_egale, egale_sym, Egx_gy.
  Qed.
  Lemma gauche_transpo: forall g x y, avoir G g -> avoir G x -> avoir G y ->
    egale (opg g x) y -> egale x (opg (invg g) y).
  Proof.
    intros g x y Gg Gx Gy Egx_y.
    rec_x_gigx x Gx g Gg.
    apply f_egale, Egx_y.
  Qed.
  Lemma droite_transpo: forall g x y, avoir G g -> avoir G x -> avoir G y ->
    egale (opg x g) y -> egale x (opg y (invg g)).
  Proof.
    intros g x y Gg Gx Gy Egx_y.
    rec_x_xgig x Gx g Gg.
    app_f_egale (fun w => opg w (invg g)). apply Egx_y.
  Qed.
  Lemma invinv_ident: forall x, avoir G x -> egale x (invg (invg x)).
  Proof.
    intros x Gx.
    apply (gauche_op_inj (invg x)); try apply ferm_inv; try apply ferm_inv; try apply Gx.
    rec_egale (@idg G). apply egale_sym, gauche_inv, Gx.
    apply droite_inv, ferm_inv, Gx.
  Qed.
  Lemma invop_opinvinv: forall x y, avoir G x -> avoir G y ->
    egale (invg (opg x y)) (opg (invg y) (invg x)).
  Proof.
    intros x y Gx Gy.
    apply gauche_transpo; try apply ferm_inv; try apply ferm_op; try apply Gx; try apply Gy.
    apply egale_sym. rec_egale (opg (invg x) idg).
    apply droite_id, ferm_inv, Gx.
    apply egale_sym. apply gauche_transpo.
    apply Gx. apply (ferm_op _ _ Gy (ferm_inv _ (ferm_op _ _ Gx Gy))).
    apply ferm_id. rec_egale (opg (opg x y) (invg (opg x y))).
    apply assoc_op; try apply ferm_inv, ferm_op; try apply Gx; try apply Gy.
    apply egale_sym, droite_inv, ferm_op. apply Gx. apply Gy.
  Qed.
  Lemma id_invid: egale (@idg G) (invg idg).
  Proof.
    apply egale_sym. rec_x_xe (@invg G idg) (@ferm_inv G _ ferm_id).
    apply egale_sym, gauche_transpo; try apply ferm_id.
    apply egale_sym, droite_id, ferm_id.
  Qed.
End GroupeTheorie.
Module Homomorphisme.
  Section ClasseDef.
    Record classe_de {dom codom:groupeTaper} := Classe {
      fonc: dom -> codom;
      carto: carto dom codom fonc;
      hom: forall x y, avoir dom x -> avoir _ y -> egale (fonc (opg x y)) (opg (fonc x) (fonc y))
    }.
    Structure taper := Paquet { dom; codom; _: @classe_de dom codom }.
    Definition classe (cT:taper) :=
      match cT return @classe_de (dom cT) (codom cT) with
      Paquet _ _ c => c end.
  End ClasseDef.
  Module Exports.
    Notation homTaper := taper.
    Definition dom {cT:taper} := dom cT.
    Definition codom {cT:taper} := codom cT.
    Definition fonc {cT:taper} := fonc (classe cT).
    Definition carto {cT:taper} := carto (classe cT).
    Definition hom {cT:taper} := hom (classe cT).
  End Exports.
End Homomorphisme.
Import Homomorphisme.Exports.
Section HomomorphismeTheorie.
  Context {phi:homTaper} (f := @fonc phi).
  Lemma hom_preserve_id: egale idg (f idg).
  Proof. 
    rec_egale (opg (invg (f idg)) (f idg)). apply gauche_inv, carto, ferm_id.
    apply egale_sym, gauche_transpo; try apply carto, ferm_id.
    rec_egale (f (opg idg idg)). apply egale_sym, hom; apply ferm_id.
    apply egale_sym. app_f_egale f. apply droite_id, ferm_id.
  Qed.
  Lemma hom_preserve_inv: forall x, avoir dom x -> egale (f (invg x)) (invg (f x)).
  Proof.
    intros x Hx.
    rec_egale (opg (invg (f x)) idg).
    -- apply gauche_transpo; try apply carto; try apply ferm_inv; try apply Hx; try apply ferm_id.
       rec_egale (f (opg x (invg x))). apply egale_sym, hom; try apply ferm_inv; try apply Hx.
       rec_egale (f idg). apply f_egale, egale_sym, droite_inv, Hx.
       apply egale_sym, hom_preserve_id.
    -- apply egale_sym, droite_id, ferm_inv, carto, Hx.
  Qed.
  Definition isomorph := remplie (fun (psi: @Homomorphisme.classe_de codom dom) =>
    et (forall h, egale h ((Homomorphisme.fonc psi) (f h))) (forall g, egale g (f ((Homomorphisme.fonc psi) g)))).
  Lemma isomorph_bij : ssi isomorph (biject (@carto phi)).
  Proof.
    apply conjonction.
     -- intros [psi [gfid fgid]]. pose (Homomorphisme.fonc psi) as g. apply conjonction.
        intros x y Efxfy. case (egale_sym (gfid x)), (egale_sym (gfid y)).
        apply f_egale. apply Efxfy.
        intros y Gy. apply (exister _ (g y)). apply fgid.
     -- intros [Hinj Hsuj]. 
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
  Definition sgnormal := forall h, avoir H h ->
   forall (g: mereg H), avoir _ g -> avoir H (opg (opg g h) (invg g)).
End SousGroupeTheorie.
Section Homomorphisme.
  Context {ht:homTaper} (f := @fonc ht) (imf := image dom f).
  Definition image_sous : sous imf codom := fun y Imy =>
    match Imy with exister _ x Px => 
      match Px with conjonction _ _ Hx Eyfx =>
        egale_ind _ _ (avoir codom) (carto x Hx) _ (egale_sym Eyfx) end end.
  Lemma image_sferm_op : forall x y, imf x -> imf y -> imf (opg x y).
  Proof. 
    intros x y Imx Imy. destruct Imx as [x' [Hx' Exfx']]. destruct Imy as [y' [Hy' Eyfy']].
    apply (exister _ (opg x' y')), conjonction.
    -- apply ferm_op. apply Hx'. apply Hy'.
    -- rec_egale (opg x (f y')). apply f_egale, Eyfy'.
       rec_egale (opg (f x') (f y')).
       app_f_egale (fun w => opg w (f y')). apply Exfx'.
       apply egale_sym, hom. apply Hx'. apply Hy'.
  Qed.
  Lemma image_sferm_inv : forall x, imf x -> imf (invg x).
  Proof.
    intros x Imx. destruct Imx as [x' [Hx' Exfx']]. 
    apply (exister _ (invg x')), conjonction.
    -- apply ferm_inv, Hx'.
    -- rec_egale (invg (f x')). apply f_egale, Exfx'.
       apply egale_sym, hom_preserve_inv, Hx'.
  Qed.
  Lemma image_sferm_id : imf idg.
  Proof. apply (exister _ idg); apply conjonction. apply ferm_id. apply hom_preserve_id. Qed.
  Definition imageSG := SousGroupe.Paquet codom (SousGroupe.Classe codom imf image_sous
    image_sferm_op image_sferm_inv image_sferm_id).

  Definition noyau : Ensemble := fun x => et (avoir dom x) (egale idg (f x)).
  Lemma noyau_sous : sous noyau dom.
  Proof. intros x Nx; apply (et_prj1 Nx). Qed.
  Lemma noyau_sferm_op : forall x y, noyau x -> noyau y -> noyau (opg x y).
  Proof.
    intros x y Nx Ny; destruct Nx as [Nx Eefx]; destruct Ny as [Ny Eefy]; apply conjonction.
    -- apply ferm_op. apply Nx. apply Ny.
    -- rec_egale (@opg (@codom ht) idg idg).
       apply droite_id, ferm_id. rec_egale (opg idg (f y)).
       apply f_egale, Eefy. rec_egale (opg (f x) (f y)).
       app_f_egale (fun w => opg w (f y)). apply Eefx.
       apply egale_sym, hom. apply Nx. apply Ny.
  Qed.
  Lemma noyau_sferm_inv : forall x, noyau x -> noyau (invg x).
  Proof.
    intros x Nx; destruct Nx as [Nx Eefx]; apply conjonction.
    -- apply ferm_inv, Nx.
    -- rec_egale (@invg (@codom ht) idg). apply id_invid.
       rec_egale (invg (f x)). apply f_egale, Eefx.
       apply egale_sym, hom_preserve_inv, Nx.
  Qed.
  Lemma noyau_sferm_id : noyau idg.
  Proof. apply conjonction. apply ferm_id. apply hom_preserve_id. Qed.
  Definition noyauSG := SousGroupe.Paquet dom (SousGroupe.Classe dom noyau noyau_sous
  noyau_sferm_op noyau_sferm_inv noyau_sferm_id).
  Lemma noyauSG_normal : sgnormal noyauSG.
  Proof.
    intros h Hh g Gg; destruct Hh as [Nh Eefh]; apply conjonction.
    -- apply ferm_op. apply ferm_op. apply Gg. apply Nh. 
       apply ferm_inv. apply Gg.
    -- rec_egale (opg (f g) (invg (f g))). apply droite_inv, carto, Gg.
       rec_egale (opg (f (opg g h)) (invg (f g))).
       assert (egale (f g) (f (opg g h))) as Efg_fgh.
       { rec_egale (opg (f g) idg). apply droite_id, carto, Gg.
         rec_egale (opg (f g) (f h)). apply f_egale, Eefh.
         apply egale_sym, hom. apply Gg. apply Nh. }
       app_f_egale (fun w => opg w (invg (f g))). apply Efg_fgh.
       rec_egale (opg (f (opg g h)) (f (invg g))).
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
  Definition cdeqde x : Ensemble := fun y => et (supp re y) (rel x y).
  Lemma cdeq_ref : forall x, supp re x -> (cdeqde x) x.
  Proof. intros x Rx. apply conjonction. apply Rx. apply rel_ref, Rx. Qed.
  Lemma ssi_rel_egcdeq : forall x y, supp re x -> supp re y ->
    ssi (rel x y) (egale (cdeqde x) (cdeqde y)).
  Proof.
    intros x y Rx Ry. apply conjonction.
    -- intros Rxy. apply egale_ens, conjonction.
    ---- intros z [Rz Rxz]. apply conjonction. apply Rz. apply (rel_trans y x z Ry Rx Rz (rel_sym _ _ Rx Ry Rxy) Rxz).
    ---- intros z [Rz Ryz]. apply conjonction. apply Rz. apply (rel_trans x y z Rx Ry Rz Rxy Ryz).
    -- intros ECxCy. apply rel_sym. apply Ry. apply Rx.
       apply (et_prj2 (egale_ind _ (cdeqde x) (fun C => C x) (cdeq_ref x Rx) (cdeqde y) ECxCy)).
  Qed.
  Lemma cdeqoverlap_rel : forall x y, supp re x -> supp re y -> 
    remplie (intsec (cdeqde x) (cdeqde y)) -> rel x y.
  Proof.
    intros x y Rx Ry [z [Cxz Cyz]]. apply (rel_trans x z y).
    apply Rx. apply (et_prj1 Cxz). apply Ry.
    apply (et_prj2 Cxz). apply rel_sym. apply Ry. apply (et_prj1 Cyz). apply (et_prj2 Cyz).
  Qed.
  Definition cdeqEnsemble : @Ensemble (@Ensemble re) :=
    fun Cx => remplie (fun y => et (supp re y) (egale (cdeqde y) Cx)).
  Lemma classedeqEns_avoir_claassedeq : forall x, supp re x -> cdeqEnsemble (cdeqde x).
  Proof. intros x Rx. apply (exister _ x). apply conjonction. apply Rx. apply egale_ref. Qed.
End ReldeqTheorie.
Section Coset.
  Context (H:sousgroupeTaper).
  Definition cosetrel_g g g' := remplie (fun h => et (avoir H h) (egale g (@opg (mereg H) g' h))).
  Definition cosetrel_d g g' := remplie (fun h => et (avoir H h) (egale g (@opg (mereg H) h g'))).
  Lemma cosetrel_g_ref : forall g, avoir (mereg H) g -> cosetrel_g g g.
  Proof. 
    intros g Gg. apply (exister _ (@idg H)), conjonction. apply ferm_id.
    rec_egale (opg g (@idg (mereg H))). apply droite_id, Gg. apply f_egale, egale_ref.
  Qed.
  Lemma cosetrel_g_sym: forall g g', avoir (mereg H) g -> avoir (mereg H) g' ->
    cosetrel_g g g' -> cosetrel_g g' g.
  Proof.
    intros g g' Gg Gg' [h [Hh Eg_g'h]]. apply (exister _ (@invg H h)), conjonction.
    -- apply ferm_inv, Hh.
    -- rec_egale (opg g (@invg (mereg H) h)). apply droite_transpo. apply sousg_sousens, Hh.
       apply Gg'. apply Gg. apply egale_sym, Eg_g'h. apply egale_ref.
  Qed.
  Lemma cosetrel_g_trans: forall g1 g2 g3, avoir (mereg H) g1 -> avoir (mereg H) g2 -> avoir (mereg H) g3 ->
    cosetrel_g g1 g2 -> cosetrel_g g2 g3 -> cosetrel_g g1 g3.
  Proof.
    intros g1 g2 g3 Gg1 Gg2 Gg3 [h12 [Hh12 Rg1g2]] [h23 [Hh23 Rg2g3]].
    apply (exister _ (@opg H h23 h12)), conjonction.
    -- apply ferm_op. apply Hh23. apply Hh12.
    -- rec_egale (opg g2 h12). apply Rg1g2. rec_egale (opg (@opg (mereg H) g3 h23) h12).
       app_f_egale (fun w => opg w h12). apply Rg2g3.
       apply egale_sym. rec_egale (opg g3 (@opg (mereg H) h23 h12)).
       apply egale_ref. apply assoc_op. apply Gg3. apply sousg_sousens, Hh23. apply sousg_sousens, Hh12.
  Qed.
  Definition coset_g := Reldeq.Paquet _ (mereg H) (Reldeq.Classe _ _ cosetrel_g
    cosetrel_g_ref cosetrel_g_sym cosetrel_g_trans).
  Definition cosetEns_g := @cdeqEnsemble coset_g.

  Lemma cosetrel_d_ref : forall g, avoir (mereg H) g -> cosetrel_d g g.
  Proof. 
    intros g Gg. apply (exister _ (@idg H)), conjonction. apply ferm_id.
    rec_egale (opg (@idg (mereg H)) g). apply gauche_id, Gg. apply f_egale, egale_ref.
  Qed.
  Lemma cosetrel_d_sym: forall g g', avoir (mereg H) g -> avoir (mereg H) g' ->
    cosetrel_d g g' -> cosetrel_d g' g.
  Proof.
    intros g g' Gg Gg' [h [Hh Eg_hg']]. apply (exister _ (@invg H h)), conjonction.
    -- apply ferm_inv, Hh.
    -- rec_egale (opg (@invg (mereg H) h) g). apply gauche_transpo. apply sousg_sousens, Hh.
       apply Gg'. apply Gg. apply egale_sym, Eg_hg'. apply egale_ref.
  Qed.
  Lemma cosetrel_d_trans: forall g1 g2 g3, avoir (mereg H) g1 -> avoir (mereg H) g2 -> avoir (mereg H) g3 ->
    cosetrel_d g1 g2 -> cosetrel_d g2 g3 -> cosetrel_d g1 g3.
  Proof.
    intros g1 g2 g3 Gg1 Gg2 Gg3 [h12 [Hh12 Rg1g2]] [h23 [Hh23 Rg2g3]].
    apply (exister _ (@opg H h12 h23)), conjonction.
     -- apply ferm_op. apply Hh12. apply Hh23.
     -- rec_egale (opg h12 g2). apply Rg1g2. 
        rec_egale (@opg (mereg H) h12 (@opg (mereg H) h23 g3)).
        apply f_egale, Rg2g3. apply egale_sym.
        rec_egale (opg (@opg (mereg H) h12 h23) g3).
        apply egale_ref. apply egale_sym, assoc_op. apply sousg_sousens, Hh12. apply sousg_sousens, Hh23. apply Gg3.
  Qed.
  Definition coset_d := Reldeq.Paquet _ (mereg H) (Reldeq.Classe _ _ cosetrel_d
    cosetrel_d_ref cosetrel_d_sym cosetrel_d_trans).
  Definition cosetEns_d := @cdeqEnsemble coset_d.
  
  Context (H_normal: sgnormal H).
  Lemma coseteg_gd_brut : forall g, avoir (mereg H) g -> forall h, avoir H h ->
    remplie (fun h' => et (avoir H h') (egale (@opg (mereg H) g h) (opg h' g))).
  Proof.
    intros g Gg h Hh. apply (exister _ (opg (opg g h) (invg g))), conjonction.
    -- apply H_normal. apply Hh. apply Gg.
    -- assert (forall x, avoir (mereg H) x -> egale x (opg (opg x (invg g)) g)) as Ex_xxinvgg.
       { intros x Gx. rec_egale (opg x idg). apply droite_id, Gx. 
         rec_egale (opg x (opg (invg g) g)). apply f_egale, gauche_inv, Gg.
         apply assoc_op. apply Gx. apply ferm_inv, Gg. apply Gg. }
       apply Ex_xxinvgg, ferm_op. apply Gg. apply sousg_sousens, Hh.
  Qed.
  Lemma coseteg_dg_brut : forall g, avoir (mereg H) g -> forall h, avoir H h ->
    remplie (fun h' => et (avoir H h') (egale (@opg (mereg H) h g) (opg g h'))).
  Proof.
    intros g Gg h Hh. destruct (coseteg_gd_brut (invg g) (ferm_inv _ Gg) h Hh) as [h' [Hh' E]].
    apply (exister _ h'), conjonction. apply Hh'. 
    case (egale_sym (invinv_ident _ Gg)).
    apply gauche_transpo. apply ferm_inv, Gg. apply ferm_op. apply sousg_sousens, Hh.
    apply ferm_inv, ferm_inv, Gg. apply sousg_sousens, Hh'. 
    case (egale_sym (assoc_op _ _ _ (ferm_inv _ Gg) (sousg_sousens _ _ Hh) (ferm_inv _ (ferm_inv _ Gg)))).
    apply egale_sym, (droite_transpo _ _ _ (ferm_inv _ Gg) (sousg_sousens _ _ Hh') (ferm_op _ _ (ferm_inv _ Gg) (sousg_sousens _ _ Hh))).
    apply egale_sym, E.
  Qed.
  Lemma coseteg_gd : forall g, avoir (mereg H) g ->
    egale (@cdeqde coset_g g) (@cdeqde coset_d g).
  Proof.
    intros g Gg. apply egale_ens, conjonction.
     -- intros g' [Gg' [h [Hh E]]]. apply conjonction. apply Gg'.
        case (egale_sym E). apply coseteg_gd_brut. apply Gg'. apply Hh.
     -- intros g' [Gg' [h [Hh E]]]. apply conjonction. apply Gg'.
        case (egale_sym E). apply coseteg_dg_brut. apply Gg'. apply Hh.
  Qed.
  Lemma cosetEnseg_gd : egale cosetEns_g cosetEns_d.
  Proof. 
    apply egale_ens, conjonction; intros Cg [g [Gg ECgCg]]; apply (exister _ g), conjonction; try apply Gg. 
    rec_egale (@cdeqde coset_g g). apply egale_sym, coseteg_gd, Gg. apply ECgCg.
    rec_egale (@cdeqde coset_d g). apply coseteg_gd, Gg; apply ECgCg. apply ECgCg.
  Qed.
  Definition cosetop (g1H g2H: @Ensemble (mereg H)) : Ensemble := 
    fun g => remplie (fun g1' => et (g1H g1') (remplie 
      (fun g2' => et (g2H g2') (egale (@opg (mereg H) g1' g2') g)))).
  (* avoir H (opg g1' g) と g1H g1' から avoir G g を復元できない assoc_op を使うには G g が必要なので。 *)
  Definition cosetinv (g1H: @Ensemble (mereg H)) : Ensemble :=
    fun g => et (avoir (mereg H) g) (remplie (fun g1' => et (g1H g1') (avoir H (opg g1' g)))).
  Definition cosetid := @cdeqde coset_g (@idg (mereg H)).
  Lemma coset_analog_op : forall g1 g2, avoir (mereg H) g1 -> avoir (mereg H) g2 ->
    egale (cosetop (@cdeqde coset_g g1) (@cdeqde coset_g g2))
    (@cdeqde coset_g (opg g1 g2)).
  Proof.
    intros g1 g2 Gg1 Gg2. apply egale_ens, conjonction.
     -- intros g [g1' [[Gg1' [h1 [Hh1 E1]]] [g2' [[Gg2' [h2 [Hh2 E2]]] E]]]]. apply conjonction.
        case E. apply ferm_op. apply Gg1'. apply Gg2'.
        destruct (coseteg_dg_brut g2' Gg2' h1 Hh1) as [h1' [Hh1' E3]].
        apply (exister _ (@opg (mereg H) h1' h2)), conjonction.
        apply (fun Hw => egale_ind _ (@opg H h1' h2) (avoir H) Hw). apply ferm_op. apply Hh1'. apply Hh2.
        apply egale_ref. case E. apply egale_sym.
        rec_egale (opg g1' (opg g2' (opg h1' h2))).
        apply egale_sym, assoc_op. apply Gg1'. apply Gg2'. apply ferm_op; apply sousg_sousens.
        apply Hh1'. apply Hh2. rec_egale (opg g1' (opg (opg g2' h1') h2)).
        apply f_egale. rec_egale (opg g2' (@opg (mereg H) h1' h2)).
        apply egale_ref. apply assoc_op. apply Gg2'. apply sousg_sousens, Hh1'. apply sousg_sousens, Hh2.
        case E3. rec_egale (opg g1' (opg h1 (opg g2' h2))).
        apply f_egale, egale_sym. rec_egale (@opg (mereg H) h1 (@opg (mereg H) g2' h2)).
        apply egale_ref. apply assoc_op. apply sousg_sousens, Hh1. apply Gg2'. apply sousg_sousens, Hh2.
        case E2. rec_egale (opg (opg g1' h1) g2). rec_egale (opg g1' (@opg (mereg H) h1 g2)).
        apply egale_ref. apply assoc_op. apply Gg1'. apply sousg_sousens, Hh1. apply Gg2.
        case E1. apply egale_ref.
     -- intros g [Gg [h [Hh E]]]. apply (exister _ g1), conjonction.
        apply cdeq_ref, Gg1. apply (exister _ (opg g2 (invg h))), conjonction.
        apply conjonction. apply ferm_op. apply Gg2. apply sousg_sousens, ferm_inv, Hh.
        apply (exister _ h), conjonction. apply Hh.
        apply egale_sym. rec_egale (opg g2 (@opg (mereg H) (@invg (mereg H) h) h)).
        apply egale_sym, assoc_op. apply Gg2. apply sousg_sousens, ferm_inv, Hh. apply sousg_sousens, Hh.
        case gauche_inv. apply sousg_sousens, Hh. apply egale_sym, droite_id, Gg2.
        rec_egale (opg (opg g1 g2) (invg h)). apply assoc_op. apply Gg1. apply Gg2. apply sousg_sousens, ferm_inv, Hh.
        case (egale_sym E). case assoc_op. apply Gg. apply sousg_sousens, Hh. apply sousg_sousens, ferm_inv, Hh.
        rec_egale (opg g (@idg (mereg H))). apply f_egale, egale_sym. rec_egale (@opg (mereg H) h (@invg (mereg H) h)).
        apply droite_inv, sousg_sousens, Hh. apply egale_ref. apply egale_sym, droite_id, Gg.
  Qed.
  Lemma coset_analog_inv : forall g, avoir (mereg H) g ->
    egale (cosetinv (@cdeqde coset_g g)) (@cdeqde coset_g (invg g)).
  Proof.
    intros g Gg. apply egale_ens, conjonction.
     -- intros ig' [Gig' [g' [[Gg' [h [Hh Eg_g'h]]] Hg'ig']]].
        destruct (coseteg_dg_brut ig' Gig' (invg h) (ferm_inv _ Hh)) as [h' [Hh' E2]].
        apply conjonction. apply Gig'.
        apply (exister _ (@opg (mereg H) h' (invg (opg g' ig')))), conjonction.
        apply (fun Hw => egale_ind _ (opg h' (@invg H (opg g' ig'))) (avoir H) Hw).
        apply ferm_op. apply Hh'. apply ferm_inv, Hg'ig'. apply egale_ref.
        apply egale_sym. rec_egale (opg (opg ig' h') (invg (opg g' ig'))).
        apply assoc_op. apply Gig'. apply sousg_sousens, Hh'. apply ferm_inv, sousg_sousens, Hg'ig'.
        case E2. case (egale_sym (invop_opinvinv g' ig' Gg' Gig')).
        rec_egale (opg (opg (opg (@invg (mereg H) h) ig') (invg ig')) (invg g')).
        apply assoc_op. apply ferm_op. apply ferm_inv, sousg_sousens, Hh.
        apply Gig'. apply ferm_inv, Gig'. apply ferm_inv, Gg'.
        rec_egale (opg (opg (@invg (mereg H) h) (opg ig' (invg ig'))) (invg g')).
        app_f_egale (fun w => opg w (invg g')). apply egale_sym, assoc_op.
        apply ferm_inv, sousg_sousens, Hh. apply Gig'. apply ferm_inv, Gig'.
        case (droite_inv ig' Gig'). case (droite_id (@invg (mereg H) h) (ferm_inv _ (sousg_sousens _ _ Hh))).
        case (invop_opinvinv). apply Gg'. apply sousg_sousens, Hh. apply f_egale. apply egale_sym, Eg_g'h.
     -- intros ig' [Gig' [h [Hh E1]]]. apply conjonction. apply Gig'.
        apply (exister _ g), conjonction. apply cdeq_ref, Gg.
        assert (egale g (opg (@invg (mereg H) h) (invg ig'))) as E.
        { case invop_opinvinv. apply Gig'. apply sousg_sousens, Hh.
          case (egale_sym (invinv_ident g Gg)). apply f_egale, E1. }
        assert (egale (invg h) (opg g ig')) as E2.
        { rec_egale (@invg (mereg H) h). apply egale_ref.
          case (egale_sym (invinv_ident _ Gig')). apply droite_transpo.
          apply ferm_inv, Gig'. apply ferm_inv, sousg_sousens, Hh. apply Gg.
          apply egale_sym, E. }
        case E2. apply ferm_inv, Hh.
  Qed.
  Lemma coset_ferm_op : forall g1H g2H, cosetEns_g g1H ->
    cosetEns_g g2H -> cosetEns_g (cosetop g1H g2H).
  Proof.
    intros g1H g2H [g1' [Gg1' Eg1H]] [g2' [Gg2' Eg2H]].
    case Eg1H, Eg2H. case (egale_sym (coset_analog_op g1' g2' Gg1' Gg2')).
    apply (exister _ (opg g1' g2')), conjonction. apply ferm_op. apply Gg1'. apply Gg2'.
    apply egale_ref.
  Qed.
  Lemma cosetid_H : egale cosetid H.
  Proof. 
    apply egale_ens, conjonction; intros h. 
     -- intros [Gh [h' [Hh' Ee_hh']]]. 
        assert (egale h (opg idg (@invg H h'))) as Eh_einvgh'.
        { rec_egale (opg idg (@invg (mereg H) h')).
          apply droite_transpo. apply sousg_sousens, Hh'. 
          apply Gh. apply ferm_id. apply egale_sym, Ee_hh'.
          apply egale_ref. }
        apply (fun Hw => egale_ind _ _ (fun w => avoir H w) Hw _ (egale_sym Eh_einvgh')).
        apply ferm_op. apply ferm_id. apply ferm_inv, Hh'.
     -- intros Hh. apply conjonction. apply sousg_sousens, Hh.
        apply (exister _ (@invg H h)), conjonction. apply ferm_inv, Hh.
        rec_egale (@idg H). apply egale_ref. rec_egale (@opg H h (@invg H h)). apply droite_inv, Hh.
        apply egale_ref.
  Qed.
  Lemma coset_ferm_inv : forall gH, 
    cosetEns_g gH -> cosetEns_g (cosetinv gH).
  Proof.
    intros gH [g' [Gg' E]]. case E. case (egale_sym (coset_analog_inv _ Gg')).
    apply (exister _ (invg g')), conjonction. apply ferm_inv, Gg'. apply egale_ref.
  Qed.
  Lemma coset_ferm_id : cosetEns_g cosetid.
  Proof. apply (exister _ idg), conjonction. apply ferm_id. apply egale_ens, conjonction; intros g H0; apply H0. Qed.
  Lemma coset_assoc_op : forall g1H g2H g3H, cosetEns_g g1H ->
    cosetEns_g g2H -> cosetEns_g g3H ->
    egale (cosetop g1H (cosetop g2H g3H)) (cosetop (cosetop g1H g2H) g3H).
  Proof.
    intros g1H g2H g3H [g1' [Gg1' Eg1H]] [g2' [Gg2' Eg2H]] [g3' [Gg3' Eg3H]].
    case Eg1H, Eg2H, Eg3H.
    case (egale_sym (coset_analog_op g2' g3' Gg2' Gg3')).
    case (egale_sym (coset_analog_op g1' (opg g2' g3') Gg1' (ferm_op _ _ Gg2' Gg3'))).
    case (egale_sym (coset_analog_op g1' g2' Gg1' Gg2')).
    case (egale_sym (coset_analog_op (opg g1' g2') g3' (ferm_op _ _ Gg1' Gg2') Gg3')).
    apply f_egale. apply assoc_op. apply Gg1'. apply Gg2'. apply Gg3'.
  Qed.
  Lemma coset_droite_id: forall g1H, cosetEns_g g1H -> egale g1H (cosetop g1H cosetid).
  Proof.
    intros g1H [g1' [Gg1' Eg1H]]. case Eg1H. unfold cosetid.
    case  (egale_sym (coset_analog_op g1' idg Gg1' ferm_id)).
    apply f_egale, droite_id, Gg1'.
  Qed.
  Lemma coset_gauche_inv : forall gH, cosetEns_g gH -> egale cosetid (cosetop (cosetinv gH) gH).
  Proof.
    intros gH [g' [Gg' EgH]]. case EgH. case (egale_sym (coset_analog_inv _ Gg')).
    case (egale_sym (coset_analog_op _ _ (ferm_inv _ Gg') Gg')).
    case gauche_inv. apply Gg'. apply egale_ref.
  Qed.
  Lemma coset_droite_inv : forall gH, cosetEns_g gH -> egale cosetid (cosetop gH (cosetinv gH)).
  Proof.
    intros gH [g' [Gg' EgH]]. case EgH. case (egale_sym (coset_analog_inv _ Gg')).
    case (egale_sym (coset_analog_op _ _ Gg' (ferm_inv _ Gg'))).
    case droite_inv. apply Gg'. apply egale_ref.
  Qed.
  Definition cosetGroupe := Groupe.Paquet _ (Groupe.Classe _ cosetEns_g
    cosetop cosetinv cosetid coset_ferm_op coset_ferm_inv
    coset_ferm_id coset_assoc_op coset_droite_id coset_gauche_inv coset_droite_inv).
End Coset.
