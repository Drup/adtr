open Syntax

(** Definition and utilities for rewrite constructs *)

(** [position] describes where a variable is allocated *)
type 'a position =
  | Internal of 'a (** The variable is present in the term *)
  | External (** The variable comes from outside, for instance the arguments *)
  | Absent (** The variable is not used *)

type 'a movement = {
  name : Name.t ;
  src : 'a position ;
  dest : 'a position ;
  ty : Syntax.type_expr ;
}

type 'a clause = 'a movement list

type 'a t = {
  f : name ;
  parameters : (name * type_expr) list;
  return_ty: type_expr;
  discriminant: name;
  discriminant_ty: type_expr;
  clauses : 'a clause list;
}


(** Printers *)

let pp_position pp_mem fmt = function
  | Internal c -> pp_mem fmt c
  | External -> Fmt.pf fmt "x"
  | Absent -> Fmt.pf fmt "ø"

let pp_clause pp_mem =
  let pp_def fmt { name ; src ; dest ; ty } =
    Fmt.pf fmt "(%s:%a -- %a → %a)"
      name Types.pp ty (pp_position pp_mem) src (pp_position pp_mem) dest
  in
  Fmt.vbox @@ Fmt.list pp_def

let pp pp_mem fmt
    { f; parameters; return_ty; discriminant; discriminant_ty; clauses } =
  Fmt.pf fmt "@[<v>@[<v2>@[%a@ (%a)@ : %a@ = rewrite %a @]{@ %a@]@ }@]"
    Name.pp f
    (Fmt.list @@ Fmt.pair ~sep:(Fmt.unit " : ") Name.pp Types.pp) parameters
    Types.pp return_ty
    Name.pp discriminant
    (Fmt.vbox @@ Fmt.list @@ Fmt.prefix (Fmt.unit "| ") @@ pp_clause pp_mem)
    clauses

(** Translate cursor-based view to mem-based view *)

module Mem = struct

  type t =
    | Cell of Cursor.path
    | Layer of Name.t * Cursor.path
  let pp fmt = function
    | Cell p -> Fmt.pf fmt "Cell(%a)" Cursor.pp p
    | Layer (k,p) -> Fmt.pf fmt "Layer(%a,%a)" Name.pp k Cursor.pp p

  let conflict mem1 mem2 =
    match mem1, mem2 with
    | Cell p1, Cell p2 -> if Cursor.overlap p1 p2 then Some Cursor.empty else None
    | Layer (_, p1), Layer (_, p2) ->
      CCOpt.map (function
          | `left, p -> (p : Cursor.path :> Cursor.cursor)
          | `right, p -> Cursor.invert p)
        @@ Cursor.conflict p1 p2
    | _ -> None
end

let map_position f = function
  | Internal x -> Internal (f x)
  | Absent -> Absent
  | External -> External
let cell p = Mem.Cell p
let layer k p = Mem.Layer(k,p)

let conflict pos1 pos2 = match pos1, pos2 with
  | Internal p1, Internal p2 -> Cursor.conflict p1 p2
  | _ -> None

let complement_path tyenv ty path0 =
  let rec aux curr_path = function
    | [] -> [], []
    | `Multiple _ :: _ ->
      (* We always introduce multiple path on both side, therefor, they should
         never appear in diffs *)
      assert false
    | `Down (constr, i) as f :: path ->
      let all_fields = Types.get_definition tyenv ty in
      let cell_paths, compl_paths =
        CCList.partition_filter_map
          (fun (constr',i',ty') ->
             if i = i' && ty = ty'
             then begin
               if constr = constr' then `Drop
               else `Left Cursor.(curr_path +/ down constr' i')
             end
             else `Right (Cursor.(curr_path +/ down constr' i'), ty'))
          all_fields
      in
      let cell_paths', compl_paths' = aux Cursor.(curr_path +/ f) path in
      (curr_path :: cell_paths @ cell_paths'), compl_paths @ compl_paths'
  in
  aux Cursor.empty path0

let cursor2mem tyenv r =
  let rec transl_movement { name ; ty ; src ; dest } =
    if Types.is_scalar ty then
      let src = map_position cell src in
      let dest = map_position cell dest in
      [{name ; ty ; src ; dest }]
    else
      match conflict src dest with
      | Some (_, vector) ->
        Report.infof "Rewrite"
          "@[%a ⋈ %a = %a@]@."
          (pp_position Cursor.pp) src
          (pp_position Cursor.pp) dest
          Cursor.pp vector;
        let k = Name.fresh "k" in
        let middle_path = [`Multiple (k, vector)] in
        let cell_suffixes, cursor_suffixes =
          complement_path tyenv ty vector
        in
        Report.infof "Rewrite"
          "@[<v>Movement:%a@,Cell:%a@,Moves:%a@]@."
          Cursor.pp vector
          Fmt.(box @@ Dump.list Cursor.pp) cell_suffixes
          Fmt.(box @@ Dump.list @@ (fun fmt (p,c) -> Fmt.pf fmt "%a/%a" Cursor.pp p Types.pp c)) cursor_suffixes;
        let cell_moves =
          let mk_move suff =
            let f =
              map_position (fun pref -> cell @@ (pref @ middle_path @ suff))
            in
            let name = Fmt.strf "%s%a" name Cursor.pp suff in
            let src = f src in
            let dest = f dest in
            { name ; src ; dest ; ty }
          in
          List.map mk_move cell_suffixes
        in
        let cursor_moves = 
          let mk_move (suff, ty) =
            let f =
              map_position (fun pref -> pref @ middle_path @ suff)
            in
            let name = Fmt.strf "%s%a" name Cursor.pp suff in
            let src = f src in
            let dest = f dest in
            transl_movement { name ; src ; dest ; ty }
          in
          CCList.flat_map mk_move cursor_suffixes
        in
        cell_moves @ cursor_moves
      | None ->
        let k = Name.fresh "k" in
        let src = map_position (layer k) src in
        let dest = map_position (layer k) dest in
        [{name ; ty ; src ; dest}]
  in
  let make_clause old_clause =
    CCList.flat_map transl_movement old_clause
  in    
  { r with clauses = List.map make_clause r.clauses }

module type MEM = sig
  type t
  val pp : t Fmt.t
  
  type conflict
  val pp_conflict : conflict Fmt.t
  val default : conflict

  val conflict : t -> t -> conflict option
end

module DepGraph (Mem : MEM) = struct
  module Vertex = struct
    type t = Mem.t movement
    let compare = Stdlib.compare
    let equal x y = compare x y = 0
    let hash x = Hashtbl.hash x
  end
  module Edge = struct
    type t = Mem.conflict
    let default = Mem.default
    let compare = compare
  end
  module G = Graph.Persistent.Digraph.ConcreteLabeled(Vertex)(Edge)
  include G

  let conflict pos1 pos2 = match pos1, pos2 with
    | Internal p1, Internal p2 -> Mem.conflict p1 p2
    | _ -> None
  let happens_before def1 def2 =
    conflict def1.src def2.dest
  let add_conflict g def1 def2 =
    let g =
      match happens_before def1 def2 with
      | Some i -> add_edge_e g (def1, i, def2)
      | None -> g
    in
    match happens_before def2 def1 with
    | Some i -> add_edge_e g (def2, i, def1)
    | None -> g
  
  let create (moves : _ clause) =
    (* let is_interesting_moves def =
     *   not (def.src = def.dest || def.dest = Absent)
     * in
     * let moves =
     *   List.filter is_interesting_moves moves
     * in *)

    List.fold_left (fun g def1 ->
        let g = add_vertex g def1 in
        List.fold_left (fun g def2 ->
            add_conflict g def1 def2
          ) g moves
      ) empty moves

  module Dot = struct
    module G = struct
      include G
          
      let graph_attributes _g = [ `Rankdir `LeftToRight ]
      let default_vertex_attributes _g = []
      let vertex_name def = "\"" ^ def.name ^ "\""
      let vertex_attributes {name;src;dest;ty} =
        let shape =
          if Types.is_scalar ty then `Shape `Ellipse else `Shape `Box
        in
        let label =
          Fmt.str "%a\n%a\n%a → %a"
            Name.pp name Types.pp ty
            (pp_position Mem.pp) src (pp_position Mem.pp) dest
        in
        [shape; `Label label]
      let default_edge_attributes _g = []
      let edge_attributes (def1,i,def2) =
        let label = Fmt.str "%a" Mem.pp_conflict i
        in
        [ `Label label;
        ]
      let get_subgraph _v = None
    end

    include Graph.Graphviz.Dot(G)
  end
  let pp_dot = Dot.fprint_graph
end

module WithCursor = DepGraph(struct
    type t = Cursor.path
    let pp = Cursor.pp
    type conflict = Cursor.cursor
    let pp_conflict = Cursor.pp_cursor
    let default = Cursor.empty
    let conflict p1 p2 =
      Cursor.conflict p1 p2 |> CCOpt.map @@ function
      | `left, p -> (p : t :> conflict)
      | `right, p -> Cursor.invert p
  end)

module WithMem = DepGraph(struct
    include Mem
    type conflict = Cursor.cursor
    let pp_conflict = Cursor.pp_cursor
    let default = Cursor.empty
  end)
