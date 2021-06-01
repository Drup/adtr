open Syntax

(** Definition and utilities for rewrite constructs *)

(** [position] describes where this variable is allocated *)
type position =
  | Internal of Cursor.path (** The variable is present in the term *)
  | External (** The variable comes from outside, for instance the arguments *)
  | Absent (** The variable is not used *)

type def = {
  src : position ;
  dest : position ;
  ty : Syntax.type_expr ;
}
type clause = def Name.Map.t

type t = {
  f : name ;
  parameters : (name * type_expr) list;
  return_ty: type_expr;
  discriminant: name;
  discriminant_ty: type_expr;
  clauses : clause list;
}


(** Printers *)

let pp_position fmt = function
  | Internal c -> Cursor.pp fmt c
  | External -> Fmt.pf fmt "x"
  | Absent -> Fmt.pf fmt "ø"

let pp_clause =
  let pp_def fmt (name, { src ; dest ; ty }) =
    Fmt.pf fmt "(%s:%a -- %a → %a)"
      name Types.pp ty pp_position src pp_position dest
  in
  Fmt.vbox @@ Fmt.iter_bindings Name.Map.iter pp_def
  
let pp fmt
    { f; parameters; return_ty; discriminant; discriminant_ty; clauses } =
  Fmt.pf fmt "@[<v>@[<v2>@[%a@ (%a)@ : %a@ = rewrite %a @]{@ %a@]@ }@]"
    Name.pp f
    (Fmt.list @@ Fmt.pair ~sep:(Fmt.unit " : ") Name.pp Types.pp) parameters
    Types.pp return_ty
    Name.pp discriminant
    (Fmt.vbox @@ Fmt.list @@ Fmt.prefix (Fmt.unit "| ") pp_clause)
    clauses
