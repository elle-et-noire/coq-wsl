
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

val sub : int -> int -> int

type reflect =
| ReflectT
| ReflectF

val iffP : bool -> reflect -> reflect

val idP : bool -> reflect

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqn : int -> int -> bool

val eqnP : int Equality.axiom

val nat_eqMixin : int Equality.mixin_of

val nat_eqType : Equality.coq_type

val subn_rec : int -> int -> int

val subn : int -> int -> int

val leq : int -> int -> bool

val slide : int -> int list -> int * int list

module NaiveSort :
 sig
  type splpair = (int list * int list)

  type spsingle = int list

  val slidefb : int list -> int -> int list -> int list * int list

  val slidefb_coat : int list -> int list -> int -> splpair -> splpair

  val sort_kernel_func :
    int list -> int list -> (int, splpair) sigT -> spsingle

  val sort_kernel : int list -> int list -> int -> splpair -> spsingle

  val n : int list -> int

  val nill : int list -> splpair

  val sort : int list -> int list
 end
