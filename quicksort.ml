
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app :
    'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
 end

(** val filter :
    ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 ->
  if f x
  then x :: (filter f l0)
  else filter f l0

(** val filter_lte :
    int -> int list -> int list **)

let filter_lte a list0 =
  filter (fun n -> (<=) n a) list0

(** val filter_gt :
    int -> int list -> int list **)

let filter_gt a list0 =
  filter (fun n -> negb ((<=) n a)) list0

(** val quicksort : int list -> int list **)

let rec quicksort = function
| [] -> []
| h :: t ->
  let sorted_t = quicksort t in
  app (filter_lte h sorted_t)
    (h :: (filter_gt h sorted_t))
