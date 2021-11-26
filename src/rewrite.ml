(** Definition and utilities for rewrite constructs *)

type 'a position =
  | Position of (Name.t option * 'a) (** A position in the term under scrutiny *)
  | External of Name.t (** An external term, like an argument *)

type 'a expr =
  | Slot of 'a position
  | App of Name.t * 'a expr list
  | Constant of Syntax.constant

type 'a movement = {
  name : Id.t ;
  src : 'a expr ;
  dest : 'a option ;
  ty : Syntax.type_expr ;
}

type 'a clause = 'a movement list

type 'a t = {
  f : Name.t ;
  parameters : (Name.t * Syntax.type_expr) list;
  return_ty: Syntax.type_expr;
  discriminant: Name.t;
  discriminant_ty: Syntax.type_expr;
  clauses : 'a clause list;
}

(** Generic utilities *)

let position x = Position (None, x)

let paths_of_dest = function
  | Some x -> [x]
  | None -> []
let rec paths_of_src = function
  | Slot (Position (_,x)) -> [x]
  | Slot (External _) -> []
  | Constant _ -> []
  | App (_,l) -> CCList.flat_map paths_of_src l

let rec map_src f = function
  | Slot (Position (n,x)) -> Slot (Position (n,f x))
  | Slot (External _ as x) -> Slot x
  | Constant _ as c -> c
  | App (n, l) -> App (n, List.map (map_src f) l)

let map_dest = CCOption.map

let map_movement f { name ; src ; dest ; ty } =
  let src = map_src f src in
  let dest = map_dest f dest in
  { name ; src ; dest ; ty }

(** Printers *)

let pp_src1 pp_mem fmt = function
  | Position (None,p) -> pp_mem fmt p
  | Position (Some n,p) -> Fmt.pf fmt "%a:%a" Name.pp n pp_mem p
  | External n -> Fmt.pf fmt "%a" Name.pp n

let rec pp_src pp_mem fmt = function
  | Constant c -> Printer.constant fmt c
  | Slot x -> pp_src1 pp_mem fmt x
  | App (n, l) ->
    Fmt.pf fmt "%a(%a)"
      Name.pp n
      (Fmt.list ~sep:Fmt.comma @@ pp_src pp_mem) l

let pp_dest pp_mem fmt = function
  | Some c -> pp_mem fmt c
  | None -> Fmt.pf fmt "ø"

let pp_move pp_mem fmt { name ; src ; dest ; ty } =
  Fmt.pf fmt "@[<hv1>(%a:%a |@ @[<h>%a@] ←@ @[<h>%a@])@]"
    Id.pp name Printer.types ty
    (pp_dest pp_mem) dest
    (pp_src pp_mem) src

let pp_clause pp_mem = Fmt.vbox @@ Fmt.list @@ pp_move pp_mem 

let pp pp_mem fmt
    { f; parameters; return_ty; discriminant; discriminant_ty; clauses } =
  Fmt.pf fmt "@[<v>@[<v2>@[%a@ (%a)@ : %a@ = rewrite %a @]{@ %a@]@ }@]"
    Name.pp f
    (Fmt.list ~sep:(Fmt.any ", ") @@
     Fmt.pair ~sep:(Fmt.any " : ") Name.pp Printer.types) parameters
    Printer.types return_ty
    Name.pp discriminant
    Fmt.(vbox @@ list (any "| " ++ pp_clause pp_mem))
    clauses

(** Subtree view *)

module Subtree = struct

  include Field
  type conflict = Field.t
  let pp_conflict = Field.pp
  let default = Field.empty
  let conflict p1 p2 =
    Field.conflict p1 p2 |> CCOption.map snd
  let pp_extra = Fmt.nop

end

(** Layer view *)
module Layer = struct

  type t = Path.t
  let pp = Path.pp
  let pp_extra fmt x =
    let src_slots = paths_of_src x.src in
    let dest_slots = paths_of_dest x.dest in
    let l = src_slots @ dest_slots in
    let f = Constraint.and_ (List.map Path.Domain.make l) in
    Fmt.pf fmt "@.@[<hov>%a@]" Constraint.pp f

  type conflict = int Constraint.t
  let pp_conflict fmt = function
    | Constraint.False -> ()
    | c -> Constraint.pp fmt c
  let default : conflict = Constraint.False

  let conflict p1 p2 : conflict option =
    Encode2SMT.check_conflict p1 p2
end


type error =
  | Not_supported of Field.t movement
exception Error of error
let error e = raise @@ Error e


let subtree2layer tyenv (r : Field.t t) =
  let transl_movement_scalar mov : Path.t movement list =
    [mov]
  in
  let transl_movement_no_conflict mov =
    (* INVARIANT: src and dest are not conflicting *)
    if Types.is_scalar mov.ty then
      transl_movement_scalar mov
    else
      let k = Index.var @@ Id.fresh "k" in
      [map_movement (fun e -> Path.(e ++ wild k)) mov]
  in
  let transl_movement_conflict id ty src dest mov =
    (* Report.infof "Rewrite"
     *   "@[%a ⋈ %a = %a@]@."
     *   (pp_position Cursor.pp) src
     *   (pp_position Cursor.pp) dest
     *   Cursor.pp vector; *)
    let index = Index.var @@ Id.fresh "k" in
    let cell_suffixes, cursor_suffixes =
      Types.complement tyenv ty mov
    in
    (** TODO We should try harder to assert that all those path suffixes are 
        non-conflicting *)
    assert (
      let f ((l1,_),(l2,_)) = CCOption.is_none @@ Field.conflict l1 l2 in
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
          Path.(word (of_fields prefix) ++
                many (Path.of_fields mov) index ++
                word (of_fields suffix))
        in
        let name = Id.derive "%s%a" id Field.pp_top suffix in
        let src =  Slot (position (f src)) in
        let dest = Some (f dest) in
        { name ; src ; dest ; ty }
      in
      List.map mk_move cell_suffixes
    in
    let cursor_moves = 
      let mk_move (suffix, ty) =
        let f prefix : Path.t =
          Path.(word_of_fields prefix ++
                many (Path.of_fields mov) index ++
                word_of_fields suffix)
        in
        let name = Id.derive "%s%a" id Field.pp_top suffix in
        let src =  Slot (position (f src)) in
        let dest = Some (f dest) in
        transl_movement_no_conflict { name ; src ; dest ; ty }
      in
      CCList.flat_map mk_move cursor_suffixes
    in
    cell_moves @ cursor_moves
  in
  let transl_movement ({ name ; ty ; src ; dest } as f) =
    match src, dest with
    | Slot (Position (_, l)), Some l' when l = l' -> []
    | _, None -> []
    | _, _ when Types.is_scalar ty ->
      let f = map_movement (fun l -> Path.word_of_fields l) f in
      transl_movement_scalar f
    | Slot _ as srcs, Some dest ->
      begin match paths_of_src srcs with
        | [ src ] -> 
          begin match Field.conflict src dest with
            | Some (_, mov) ->
              transl_movement_conflict name ty src dest mov
            | None ->
              let f = map_movement (fun l -> Path.word_of_fields l) f in
              transl_movement_no_conflict f
          end
        | [] -> 
          let f = map_movement (fun l -> Path.word_of_fields l) f in
          transl_movement_no_conflict f
        | _ ->
          error @@ Not_supported f
      end
    | _ ->
      error @@ Not_supported f
  in
  let make_clause old_clause =
    CCList.flat_map transl_movement old_clause
  in    
  { r with clauses = List.map make_clause r.clauses }

module type MEM = sig
  type t
  val pp : t Fmt.t
  val pp_extra : t movement Fmt.t
  
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
    type t = Mem.conflict list
    let default = []
    let compare = compare
  end
  module G = Graph.Persistent.Digraph.ConcreteLabeled(Vertex)(Edge)
  include G
  module V = struct include V module Map = CCMap.Make(V) end
  module E = struct include E module Map = CCMap.Make(E) end

  let conflict srcs dest =
    let l = paths_of_src srcs in 
    match dest with
    | Some dest -> List.filter_map (fun src -> Mem.conflict src dest) l
    | None -> []
  let happens_before def1 def2 =
    conflict def1.src def2.dest
  let add_conflict g def1 def2 =
    if V.equal def1 def2 then
      match happens_before def1 def2 with
      | [] -> g
      | i -> add_edge_e g (def1, i, def2)
    else
      let g =
        match happens_before def1 def2 with
        | [] -> g
        | i -> add_edge_e g (def1, i, def2)
      in
      match happens_before def2 def1 with
      | [] -> g
      | i -> add_edge_e g (def2, i, def1)

  let create (moves : _ clause) =
    List.fold_left (fun g def1 ->
        let g = add_vertex g def1 in
        List.fold_left (fun g def2 ->
            add_conflict g def1 def2
          ) g moves
      ) empty moves

  module Dot = Graph.Graphviz.Dot(struct
      include G
      let graph_attributes _g = [ `Rankdir `LeftToRight ]
      let default_vertex_attributes _g = []
      let vertex_name def =
        Fmt.str "\"%a:%a\"" Id.pp def.name Printer.types def.ty
      let vertex_attributes ({name;src;dest;ty} as x) =
        let shape =
          if Types.is_scalar ty then `Shape `Ellipse else `Shape `Box
        in
        let label =
          Fmt.str "%a\n%a\n%a ← %a%a"
            Id.pp name Printer.types ty
             (pp_dest Mem.pp) dest (pp_src Mem.pp) src
            Mem.pp_extra x
        in
        [shape; `Label label]
      let default_edge_attributes _g = []
      let edge_attributes (def1,i,def2) =
        let label = Fmt.str "@[<v>%a@]" (Fmt.list ~sep:Fmt.cut Mem.pp_conflict) i
        in
        [ `Label label;
        ]
      let get_subgraph _v = None
    end)
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

module WithSubtree = DepGraph(Subtree)
module WithLayer = DepGraph(Layer)

let prepare_error = function
  | Error (Not_supported m) -> 
    Some (Report.errorf "Not supported : %a" (pp_move @@ Field.pp) m)
  | _ -> None
let () =
  Report.register_report_of_exn prepare_error
