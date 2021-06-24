type field = { ty : Syntax.type_expr; pos : int}
type t = field list

let empty = []

let (+/) : t -> field -> t = fun a b -> a @ [b]

(** [conflict p1 p2] check if one path is prefix of the other.
    Return which one is shortest, along with the extra bits *)
let rec conflict (p1:t) (p2:t) = match p1, p2 with
  | [], l -> Some (`left, l)
  | l, [] -> Some (`right, l)
  | x1::t1, x2::t2 ->
    if x1 = x2 then conflict t1 t2
    else None

let pp_field fmt {ty;pos} = Fmt.pf fmt ".%a@%i" Printer.types ty pos
let pp = Fmt.(list ~sep:nop pp_field)
let pp_top fmt = function
  | [] -> Fmt.pf fmt "[]"
  | l -> Fmt.(list ~sep:nop pp_field) fmt l
