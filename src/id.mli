type t

val name : t -> string

val global : string -> t
val fresh : string -> t
val freshf : ('a, Format.formatter, unit, t) format4 -> 'a

val as_left : t -> t
val as_right : t -> t

val derive : (string -> 'a, Format.formatter, unit, t) format4 -> t -> 'a
    
val pp : t Fmt.t
val to_string : t -> string

include Hashtbl.HashedType with type t := t
include Set.OrderedType with type t := t

module Set : CCSet.S with type elt = t
module Map : CCMap.S with type key = t
module H : CCHashtbl.S with type key = t
