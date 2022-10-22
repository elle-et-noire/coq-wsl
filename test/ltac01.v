Require Import List.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac length' ls :=
  match ls with
  | nil => O
  | _ :: ?ls' =>
    let ls'' := length' ls' in constr: (S ls'')
  end.

Goal True.
  let n := length' (1 :: 2 :: 3 :: nil) in
  pose n.
  reflexivity.
Qed.

Ltac _map T f :=
  let rec map' ls :=
    match ls with
    | nil => constr:(@nil T)
    | ?x :: ?ls' =>
      let x' := f x in
      let ls'' := map' ls' in
      constr:(x' :: ls'')
    end in
  map'.

Check (1, 2).

Goal True.
  let ls := _map (nat * nat)%type (fun n => (n, n)) (1 :: 2 :: 3 :: nil) in
  pose ls.