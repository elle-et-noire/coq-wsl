
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

type reflect =
| ReflectT
| ReflectF

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m =
    m.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t =
  (Equality.coq_class t).Equality.op

(** val eqn : int -> int -> bool **)

let rec eqn m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      n0)
    (fun m' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n' -> eqn m' n')
      n0)
    m

(** val eqnP : int Equality.axiom **)

let eqnP n0 m =
  iffP (eqn n0 m) (idP (eqn n0 m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n0 =
  eq_op nat_eqType (Obj.magic subn m n0) (Obj.magic 0)

(** val slide : int -> int list -> int * int list **)

let rec slide i = function
| [] -> (i, [])
| h :: t ->
  if leq (Stdlib.Int.succ i) h
  then let (h', t') = slide h t in (h', (i :: t'))
  else let (i', t') = slide i t in (i', (h :: t'))

module NaiveSort =
 struct
  type splpair = (int list * int list)

  type spsingle = int list

  (** val slidefb : int list -> int -> int list -> int list * int list **)

  let slidefb l1 h t =
    let (i, l1') = slide h l1 in
    let (i', l2') = slide i t in ((app l1' (i' :: [])), l2')

  (** val slidefb_coat : int list -> int list -> int -> splpair -> splpair **)

  let slidefb_coat _ _ _ = function
  | (l1, l2) -> (match l2 with
                 | [] -> (l1, l2)
                 | h :: t -> slidefb l1 h t)

  (** val sort_kernel_func :
      int list -> int list -> (int, splpair) sigT -> spsingle **)

  let rec sort_kernel_func lst1 lst2 x =
    let n0 = projT1 x in
    let l1l2 = projT2 x in
    let sort_kernel0 = fun n1 l1l3 ->
      sort_kernel_func lst1 lst2 (ExistT (n1, l1l3))
    in
    let (_, l2) = l1l2 in
    (match l2 with
     | [] -> fst (slidefb_coat lst1 lst2 n0 l1l2)
     | _ :: _ ->
       sort_kernel0 (subn n0 (Stdlib.Int.succ 0))
         (slidefb_coat lst1 lst2 n0 l1l2))

  (** val sort_kernel : int list -> int list -> int -> splpair -> spsingle **)

  let sort_kernel lst1 lst2 n0 l1l2 =
    sort_kernel_func lst1 lst2 (ExistT (n0, l1l2))

  (** val n : int list -> int **)

  let n =
    length

  (** val nill : int list -> splpair **)

  let nill l =
    ([], l)

  (** val sort : int list -> int list **)

  let sort l =
    sort_kernel [] l (n l) (nill l)
 end
