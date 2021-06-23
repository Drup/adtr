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
    Fmt.pf fmt "@[<hv1>(%s:%a |@ @[<h>%a@] →@ @[<h>%a@])@]"
      name Types.pp ty (pp_position pp_mem) src (pp_position pp_mem) dest
  in
  Fmt.vbox @@ Fmt.list pp_def

let pp pp_mem fmt
    { f; parameters; return_ty; discriminant; discriminant_ty; clauses } =
  Fmt.pf fmt "@[<v>@[<v2>@[%a@ (%a)@ : %a@ = rewrite %a @]{@ %a@]@ }@]"
    Name.pp f
    (Fmt.list ~sep:(Fmt.unit ", ") @@
     Fmt.pair ~sep:(Fmt.unit " : ") Name.pp Types.pp) parameters
    Types.pp return_ty
    Name.pp discriminant
    (Fmt.vbox @@ Fmt.list @@ Fmt.prefix (Fmt.unit "| ") @@ pp_clause pp_mem)
    clauses

(** Translate cursor-based view to mem-based view *)

module Mem = struct

  type t = Cursor.path
  let pp = Cursor.pp_path

  let conflict mem1 mem2 =
    if Cursor.overlap mem1 mem2 then Some Cursor.empty else None
end

let map_position f = function
  | Internal x -> Internal (f x)
  | Absent -> Absent
  | External -> External
let cell p = Cursor.as_path p
let layer k p = Cursor.(as_path p ++ [`Any k])

let conflict pos1 pos2 = match pos1, pos2 with
  | Internal p1, Internal p2 -> Cursor.conflict p1 p2
  | _ -> None

let complement_path tyenv ty0 (fields0 : Cursor.fields) =
  let rec aux prev_ty curr_fields = function
    | [] -> [], []
    | `Down (ty, i) as f :: path ->
      let all_fields = Types.get_definition tyenv prev_ty in
      let compl_paths =
        CCList.sort_uniq ~cmp:Stdlib.compare @@
        CCList.filter_map
          (fun (_constr',i',ty') ->
             if i = i' && ty = ty' then None
             else Some (Cursor.(curr_fields +/ down ty' i'), ty'))
          all_fields
      in
      let curr_fields', compl_paths' = aux ty Cursor.(curr_fields +/ f) path in
      curr_fields :: curr_fields', compl_paths @ compl_paths'
  in
  aux ty0 Cursor.empty fields0

let cursor2mem tyenv (r : Cursor.fields t) =
  let transl_movement_scalar { name ; ty ; src ; dest } =
    let src = map_position cell src in
    let dest = map_position cell dest in
    [{name ; ty ; src ; dest }]
  in
  let transl_movement_no_conflict { name ; ty ; src ; dest } =
    (* INVARIANT: src and dest are not conflicting *)
    if Types.is_scalar ty then
      transl_movement_scalar { name ; ty ; src ; dest }
    else
      let k = Index.var @@ Name.fresh "k" in
      let src = map_position (layer k) src in
      let dest = map_position (layer k) dest in
      [{name ; ty ; src ; dest}]
  in
  let transl_movement { name ; ty ; src ; dest } =
    if src = dest then
      []
    else if Types.is_scalar ty then
      transl_movement_scalar { name ; ty ; src ; dest }
    else
      match conflict src dest with
      | Some (_, vector) ->
        (* Report.infof "Rewrite"
         *   "@[%a ⋈ %a = %a@]@."
         *   (pp_position Cursor.pp) src
         *   (pp_position Cursor.pp) dest
         *   Cursor.pp vector; *)
        let k = Index.var @@ Name.fresh "k" in
        let middle_path : Cursor.path = [`Multiple (k, vector)] in
        let cell_suffixes, cursor_suffixes =
          complement_path tyenv ty vector
        in
        (* Report.infof "Rewrite"
         *   "@[<v>Movement:%a@,Cells:%a@,Cursors:%a@]@."
         *   Cursor.pp vector
         *   Fmt.(box @@ Dump.list Cursor.pp) cell_suffixes
         *   Fmt.(box @@ Dump.list @@ (fun fmt (p,c) -> Fmt.pf fmt "%a/%a" Cursor.pp p Types.pp c)) cursor_suffixes; *)
        let cell_moves =
          let mk_move suff =
            let suff = Cursor.as_path suff in
            let f =
              map_position
                (fun pref -> cell Cursor.(as_path pref ++ middle_path ++ suff))
            in
            let name = Fmt.strf "%s%a" name Cursor.pp_path suff in
            let src = f src in
            let dest = f dest in
            { name ; src ; dest ; ty }
          in
          List.map mk_move cell_suffixes
        in
        let cursor_moves = 
          let mk_move (suff, ty) =
            let suff = Cursor.as_path suff in
            let f =
              map_position
                (fun pref -> Cursor.(as_path pref ++ middle_path ++ suff))
            in
            let name = Fmt.strf "%s%a" name Cursor.pp_path suff in
            let src = f src in
            let dest = f dest in
            transl_movement_no_conflict { name ; src ; dest ; ty }
          in
          CCList.flat_map mk_move cursor_suffixes
        in
        cell_moves @ cursor_moves
      | None ->
        transl_movement_no_conflict { name ; ty ; src ; dest }
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
      let vertex_name def =
        Fmt.strf "\"%s:%a\"" def.name Types.pp def.ty
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

  let show g =
    CCIO.File.with_temp ~prefix:"adt4hpc" ~suffix:".dot" (fun s ->
        CCIO.with_out s @@ fun oc -> 
        Dot.output_graph oc g;
        ignore @@ CCUnix.call "xdot %s" s
      ) 

  let create_and_show input =
    let g = create input in
    if not @@ is_empty g then show g
end

module WithCursor = DepGraph(struct
    type t = Cursor.fields
    let pp = Cursor.pp
    type conflict = Cursor.fields
    let pp_conflict = Cursor.pp
    let default = Cursor.empty
    let conflict p1 p2 =
      Cursor.conflict p1 p2 |> CCOpt.map @@ function
      | `left, p -> (p : t :> conflict)
      | `right, p -> (p : t :> conflict)
  end)

module WithMem = DepGraph(struct
    include Mem
    type conflict = Cursor.path
    let pp_conflict = Cursor.pp_path
    let default = Cursor.empty
  end)
