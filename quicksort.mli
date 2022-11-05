
val negb : bool -> bool

val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
 end

val filter :
  ('a1 -> bool) -> 'a1 list -> 'a1 list

val filter_lte : int -> int list -> int list

val filter_gt : int -> int list -> int list

val quicksort : int list -> int list
