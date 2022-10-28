Inductive uo : Prop :=
  gue : forall n:nat, uo.
Definition uouo (H: True) := 
  match H with I => 1 end.
Definition gwa (H: uo) :=
  match H with gue n => n end.
Definition gwa {A:Type} (P: A -> Prop) (H: uo P) :=
  match H with gue _ a _ => a end.