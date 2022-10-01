
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


(*===== Reflexion =====*)

Definition estvraie (b : booleenne) := 
  match b with
  | vraie => Vraie
  | faux => Faux
  end.

Inductive refleter (P : Prop) : booleenne -> Set :=
  | refletervraie : P -> refleter P vraie
  | refleterfaux : (nepas P) -> refleter P faux.

Lemma iffP : forall (P Q : Prop) (b : booleenne),
  refleter P b -> (P -> Q) -> (Q -> P) -> refleter Q b.
Proof.
  intros P Q b HPb HPQ HQP.
  case HPb; intros HP.
  - apply refletervraie. apply HPQ; apply HP.
  - apply refleterfaux. unfold nepas. intros HQ. unfold nepas in HP. apply HQP in HQ. apply HP in HQ. case HQ.
Qed.

Lemma idP : forall (b : booleenne), refleter (estvraie b) b.
Proof.
  intros b.
  case b.
  - apply refletervraie. apply identite.
  - apply refleterfaux. unfold nepas. simpl. apply Faux_ind.
Qed.

Record melange (T : Type) :=
  EgMelange {
    op : T -> T -> booleenne;
    a : forall x y : T, refleter (egale _ x y) (op x y)
  }.

Record egtaper :=
  EgTaper {
    sorte : Type;
    mel : melange sorte
  }.

Check op : forall (T : Type), melange T -> T -> T -> booleenne.

Definition eg_op (T : egtaper) := op (sorte T) (mel T).
Check eg_op : forall (T : egtaper), (sorte _) -> (sorte _) -> booleenne.

Lemma egP : forall (T : egtaper) (x y : sorte T), refleter (egale _ x y) (eg_op _ x y).
Proof.
  intro T.
  case T.
  intros t m x y.
  case m.
  intros op a.
  apply a.
Qed.

Lemma introVraieFaux : forall (P : Prop) (b c : booleenne), refleter P b ->
  (match c with
  | vraie => P
  | faux => nepas P
  end) -> egale _ b c.
Proof.
  intros P b c Hb.
  case c; case Hb; intros H1 H2.
  - apply (egreflexion _ vraie).
  - apply H1 in H2. case H2.
  - apply H2 in H1. case H1.
  - apply egreflexion.
Qed.

Lemma elimVraieFaux : forall (P : Prop) (b c : booleenne), refleter P b -> egale _ b c ->
  (match c with
  | vraie => P
  | faux => nepas P
  end).
Proof.
  intros P b c Hb Hbc.
  case Hbc.
  case Hb; intro H; apply H.
Qed.

Lemma elimVraie : forall (P : Prop) (b : booleenne), refleter P b -> estvraie b -> P.
Proof.
  intros P b Hb.
  (* apply (elimVraieFaux P b vraie Hb). *)
  case Hb.
  - intros HP _. apply HP.
  - simpl. intros _ F. case F.
Qed.

Lemma introVraie : forall (P : Prop) (b : booleenne), refleter P b -> P -> estvraie b.
Proof.
  intros P b Hb.
  (* Check (introVraieFaux P b vraie Hb). *)
  case Hb.
  - intros _ _. apply identite.
  - intros NHP HP. apply NHP in HP. case HP.
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

Definition naturelle_egMelange := EgMelange naturelle egnaturelle naturelle_egP.
Definition naturelle_egTaper := @EgTaper naturelle naturelle_egMelange.
Compute (eg_op naturelle_egTaper neuf dix).

Lemma egvraie_estvraie : forall b : booleenne, egale _ b vraie -> estvraie b.
Proof. intros b H. apply egsym in H. case H. apply identite. Qed.

Lemma estvraie_egvraie : forall b : booleenne, estvraie b -> egale _ b vraie.
Proof.
  induction b.
  - intros _. apply egreflexion.
  - intros F. case F.
Qed.

Definition neufNdix (H : egale _ neuf dix) :=
  Eval compute in (egale_ind _ (eg_op naturelle_egTaper neuf dix) (fun b => estvraie (nepasb b))
   identite vraie (estvraie_egvraie _ (introVraie _ _ (egP naturelle_egTaper neuf dix) H))) .


(* ===== Ensemble ===== *)

Definition Ensemble (M: Type) := M -> Prop.
Definition ensemble (M: Type) := M -> booleenne.

Lemma axiom_ensemble : forall (M: Type) (A: ensemble M), 
  forall (x: M), estvraie (oub (A x) (nepasb (A x))).
Proof.
  intros.
  case (A x); apply identite.
Qed.

Definition appartenir (M: Type) (x: M) (ens: ensemble M) := estvraie (ens x).

Definition videenseble (M: Type): ensemble M := fun _ => faux.
Definition memeenseble (M: Type): ensemble M := fun _ => vraie.

Definition sousensemble (M: Type) (A B: ensemble M)
  := forall (x: M), appartenir _ x A -> appartenir _ x B.

(* ===== Group ===== *)

Record groupe: Type := Groupe {
  porteur: Type;
  (* support set *)
  support: ensemble porteur;
  (* operator *)
  operatrice: porteur -> porteur -> porteur;
  (* inverse *)
  inverse: porteur -> porteur;
  (* identity *)
  elemid: porteur;
  (* closure property of the operator *)
  fermer_ope: forall (x y: porteur), 
    appartenir _ x support -> appartenir _ y support
    -> appartenir _ (operatrice x y) support;
  (* closure property of taking inverse *)
  fermer_inv: forall (x: porteur),
    appartenir _ x support -> appartenir _ (inverse x) support;
  (* identity is in the group *)
  fermer_id: appartenir _ elemid support;
  (* assocciative property of the operator *)
  assoc_ope: forall (x y z: porteur),
    appartenir _ x support -> appartenir _ y support -> appartenir _ z support
    -> egale _ (operatrice (operatrice x y) z) (operatrice x (operatrice y z));
  inv_gauche: forall (x: porteur),
    appartenir _ x support -> egale _ elemid (operatrice (inverse x) x);
  inv_droite: forall (x: porteur),
    appartenir _ x support -> egale _ elemid (operatrice x (inverse x));
  id_droite: forall (x: porteur),
    appartenir _ x support -> egale _ x (operatrice x elemid)
}.

Lemma eg_loitransitive: forall (A: Type) (x y z: A),
  egale _ x y -> egale _ y z -> egale _ x z.
Proof.
  intros A x y z Hxy Hyz.
  case Hyz.
  apply Hxy.
Qed.

Lemma id_gauche: forall (G: groupe) (x: porteur G),
  appartenir _ x (support G) -> egale _ x (operatrice G (elemid G) x).
Proof.
  intros G x H.
  case (egsym _ _ _ (inv_droite G x H)).
  case (egsym _ _ _ (assoc_ope _ x (inverse _ x) x H (fermer_inv _ x H) H)).
  case (inv_gauche G x H).
  case (id_droite G x H).
  apply egreflexion.
Qed.
