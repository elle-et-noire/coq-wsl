
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val leb : int -> int -> bool **)

let rec leb n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n

(** val ltb : int -> int -> bool **)

let ltb n m =
  leb (Pervasives.succ n) m

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val flip_ltb : int -> int -> bool **)

let flip_ltb x y =
  ltb y x

(** val flip_geb : int -> int -> bool **)

let flip_geb =
  leb

(** val quickSort' : int list -> int list **)

let rec quickSort' = function
| [] -> []
| x :: xs ->
  app (quickSort' (filter (flip_ltb x) xs))
    (x :: (quickSort' (filter (flip_geb x) xs)))

(** val quickSort : int list -> int list **)

let quickSort =
  quickSort'
