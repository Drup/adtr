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

(** Generic utilities *)

let map_position f = function
  | Internal x -> Internal (f x)
  | Absent -> Absent
  | External -> External

let map_movement f { name ; src ; dest ; ty } =
  let src = map_position f src in
  let dest = map_position f dest in
  { name ; src ; dest ; ty }

(** Printers *)

let pp_position pp_mem fmt = function
  | Internal c -> pp_mem fmt c
  | External -> Fmt.pf fmt "x"
  | Absent -> Fmt.pf fmt "ø"

let pp_clause pp_mem =
  let pp_def fmt { name ; src ; dest ; ty } =
    Fmt.pf fmt "@[<hv1>(%s:%a |@ @[<h>%a@] →@ @[<h>%a@])@]"
      name Printer.types ty (pp_position pp_mem) src (pp_position pp_mem) dest
  in
  Fmt.vbox @@ Fmt.list pp_def

let pp pp_mem fmt
    { f; parameters; return_ty; discriminant; discriminant_ty; clauses } =
  Fmt.pf fmt "@[<v>@[<v2>@[%a@ (%a)@ : %a@ = rewrite %a @]{@ %a@]@ }@]"
    Name.pp f
    (Fmt.list ~sep:(Fmt.unit ", ") @@
     Fmt.pair ~sep:(Fmt.unit " : ") Name.pp Printer.types) parameters
    Printer.types return_ty
    Name.pp discriminant
    (Fmt.vbox @@ Fmt.list @@ Fmt.prefix (Fmt.unit "| ") @@ pp_clause pp_mem)
    clauses

(** Subtree view *)

module Subtree = struct

  let conflict pos1 pos2 = match pos1, pos2 with
    | Internal p1, Internal p2 -> Field.conflict p1 p2
    | _ -> None

  let complement tyenv ty0 (fields0 : Field.t) =
    let rec aux prev_ty curr_fields = function
      | [] -> [], []
      | {Field. ty; pos} as f :: path ->
        let all_fields = Types.get_definition tyenv prev_ty in
        let compl_paths =
          CCList.sort_uniq ~cmp:Stdlib.compare @@
          CCList.filter_map
            (fun (_constr',f') ->
               if f = f' then None
               else Some (Field.(curr_fields +/ f'), f'.ty))
            all_fields
        in
        let curr_fields', compl_paths' = aux ty Field.(curr_fields +/ f) path in
        curr_fields :: curr_fields', compl_paths @ compl_paths'
    in
    aux ty0 Field.empty fields0

end

(** Layer view *)
module Layer = struct

  type t = Path.t
  let pp = Path.pp
             
  type conflict = Constraint.t
  let pp_conflict fmt = function
    | Constraint.False -> ()
    | c -> Constraint.pp fmt c
  let default : conflict = Constraint.False

  let conflict p1 p2 : conflict option =
    Encode2SMT.check_conflict p1 p2

  let one (fields, mult) : Path.t = [ fields ; mult]
  let many k (fields, mult) : Path.t = [ fields ; mult ; k]
end



let subtree2layer tyenv (r : Field.t t) =
  let transl_movement_scalar mov : Path.t movement list =
    [map_movement Layer.one mov]
  in
  let transl_movement_no_conflict mov =
    (* INVARIANT: src and dest are not conflicting *)
    if Types.is_scalar mov.ty then
      transl_movement_scalar mov
    else
      let k = Index.var @@ Name.fresh "k" in
      [map_movement (Layer.many k) mov]
  in
  let transl_movement ({ name ; ty ; src ; dest } as f) =
    if src = dest then
      []
    else if Types.is_scalar ty then
      let f = map_movement (fun l -> (l, None)) f in
      transl_movement_scalar f
    else
      match Subtree.conflict src dest with
      | Some (_, mov) ->
        (* Report.infof "Rewrite"
         *   "@[%a ⋈ %a = %a@]@."
         *   (pp_position Cursor.pp) src
         *   (pp_position Cursor.pp) dest
         *   Cursor.pp vector; *)
        let index = Index.var @@ Name.fresh "k" in
        let cell_suffixes, cursor_suffixes =
          Subtree.complement tyenv ty mov
        in
        (** TODO We should try harder to assert that all those path suffixes are 
            non-conflicting *)
        assert (
          let f ((l1,_),(l2,_)) = CCOpt.is_none @@ Field.conflict l1 l2 in
          CCList.(for_all f @@ diagonal cursor_suffixes)
        );
        assert (
          let f (l1,l2) = l1 <> l2 in
          CCList.(for_all f @@ diagonal cell_suffixes)
        );
        (* Report.infof "Rewrite"
         *   "@[<v>Movement:%a@,Cells:%a@,Cursors:%a@]@."
         *   Cursor.pp vector
         *   Fmt.(box @@ Dump.list Cursor.pp) cell_suffixes
         *   Fmt.(box @@ Dump.list @@ (fun fmt (p,c) -> Fmt.pf fmt "%a/%a" Cursor.pp p Types.pp c)) cursor_suffixes; *)
        let cell_moves =
          let mk_move suffix =
            let f prefix : Path.t =
              Layer.one (prefix, Some {Path. index ; mov ; suffix })
            in
            let name = Fmt.strf "%s%a" name Field.pp_top suffix in
            let src =  map_position f src in
            let dest = map_position f dest in
            { name ; src ; dest ; ty }
          in
          List.map mk_move cell_suffixes
        in
        let cursor_moves = 
          let mk_move (suffix, ty) =
            let f pref = (pref, Some {Path. index ; mov ; suffix }) in
            let name = Fmt.strf "%s%a" name Field.pp_top suffix in
            let src = map_position f src in
            let dest = map_position f dest in
            transl_movement_no_conflict { name ; src ; dest ; ty }
          in
          CCList.flat_map mk_move cursor_suffixes
        in
        cell_moves @ cursor_moves
      | None ->
        let f = map_movement (fun l -> (l, None)) f in
        transl_movement_no_conflict f
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
        Fmt.strf "\"%s:%a\"" def.name Printer.types def.ty
      let vertex_attributes {name;src;dest;ty} =
        let shape =
          if Types.is_scalar ty then `Shape `Ellipse else `Shape `Box
        in
        let label =
          Fmt.str "%a\n%a\n%a → %a"
            Name.pp name Printer.types ty
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

module WithField = DepGraph(struct
    include Field
    type conflict = Field.t
    let pp_conflict = Field.pp
    let default = Field.empty
    let conflict p1 p2 =
      Field.conflict p1 p2 |> CCOpt.map snd
  end)

module WithPath = DepGraph(Layer)
