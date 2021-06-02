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

module DepGraph = struct
  module G = Graph.Persistent.Digraph.ConcreteLabeled(Name)(struct
      type t = int
      let default = 0
      let compare = CCOrd.int
    end)
  include G

  let conflict pos1 pos2 = match pos1, pos2 with
    | Internal p1, Internal p2 -> Cursor.conflict p1 p2
    | _ -> None
  
  let happens_before def1 def2 =
    conflict def1.src def2.dest
  let add_conflict g (name1,def1) (name2,def2) = 
    let g =
      match happens_before def1 def2 with
      | Some i -> add_edge_e g (name1, i, name2)
      | None -> g
    in
    match happens_before def2 def1 with
    | Some i -> add_edge_e g (name2, i, name1)
    | None -> g
  
  let create clause =
    Name.Map.fold (fun name1 def1 g -> 
        Name.Map.fold (fun name2 def2 g ->
            add_conflict g (name1,def1) (name2,def2)
          ) clause g
      ) clause empty

  module Topo = Graph.Topological.Make(G)
  module Dot = struct
    module G = struct
      include G
          
      let graph_attributes _g = []
      let default_vertex_attributes _g = []
      let vertex_name n = n
      let vertex_attributes _n = []
      let default_edge_attributes _g = []
      let edge_attributes (_,i,_) = [`Label (Fmt.str "%i" i) ]
      let get_subgraph _v = None
    end

    include Graph.Graphviz.Dot(G)
  end
  let pp_dot = Dot.fprint_graph
end


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
