open Syntax

type error =
  | Overlapping_name of Name.t
  | Unbound_variable of Name.t
  | Cannot_pattern_match of Syntax.type_expr
exception Error of error
let error e = raise @@ Error e

let prepare_error = function
  | Error (Overlapping_name n) ->
    Some
      (Report.errorf "This name is not allowed to be redefined: %a" Name.pp n)
  | Error (Unbound_variable n) -> 
    Some
      (Report.errorf "The variable %a is unbounded" Name.pp n)
  | Error (Cannot_pattern_match ty) ->
    Some
      (Report.errorf "This rewrite is applied to a value of type %a.@ Values of this type can't be rewriten." Types.pp ty)
  | _ -> None

let () =
  Report.register_report_of_exn prepare_error


let add_name n t e =
  if Name.Map.mem n e then
    error @@ Overlapping_name n
  else
    Name.Map.add n t e
let get_name n e =
  match Name.Map.get n e with
  | None -> error @@ Unbound_variable n
  | Some v -> v


let type_pattern tyenv posmap0 pattern0 pat_ty0 = 
  let rec aux posmap (path : Cursor.path) pattern pat_ty = match pattern with
    | PVar name ->
      add_name name (Rewrite.Internal path, pat_ty) posmap
    | PConstructor { constructor; arguments } ->
      let argument_tys =
        Types.instantiate_data_constructor tyenv constructor pat_ty
      in
      CCList.foldi2
        (fun env i pattern pat_ty ->
           aux env Cursor.(path +/ down constructor i) pattern pat_ty)
        posmap arguments argument_tys
  in
  aux posmap0 Cursor.empty pattern0 pat_ty0

let env_of_posmap posmap = Name.Map.map snd posmap

let type_expression tyenv env posmap0 expr0 expr_ty0 = 
  let rec aux posmap (path : Cursor.path) expr expr_ty = match expr with
    | EVar name ->
      let _ty = get_name name env in
      (* Types.check ty expr_ty; *)
      add_name name (Rewrite.Internal path) posmap
    | EConstructor { constructor; arguments } ->
      let argument_tys =
        Types.instantiate_data_constructor tyenv constructor expr_ty
      in
      CCList.foldi2
        (fun env i expr expr_ty ->
           aux env Cursor.(path +/ down constructor i) expr expr_ty)
        posmap arguments argument_tys
  in
  aux posmap0 Cursor.empty expr0 expr_ty0

let type_clause tyenv env (pattern, pat_ty) (expr, expr_ty) =
  let inputs = Name.Map.map (fun ty -> Rewrite.External, ty) env in
  let srcs = type_pattern tyenv inputs pattern pat_ty in
  let env =
    Name.Map.union (fun _ _ e -> Some e) env (env_of_posmap srcs)
  in
  let dests = type_expression tyenv env Name.Map.empty expr expr_ty in
  Name.Map.merge_safe srcs dests
    ~f:((fun name -> function
        | `Left (src, ty) ->
          Some {Rewrite. name ; src; dest = Absent ; ty }
        | `Right dest -> failwith "unbound var"
        | `Both ((src, ty), dest) ->
          Some {Rewrite. name ; src; dest; ty }
      ))
  |> Name.Map.values
  |> CCList.of_iter

let type_rewrite
    tyenv {Syntax. f ; parameters ; return_ty ; discriminant ; clauses } =
  let env =
    List.fold_left (fun e (n,ty) -> add_name n ty e) Name.Map.empty parameters
  in
  let discriminant_ty = get_name discriminant env in
  let env = 
    Name.Map.remove discriminant env
  in
  let clauses =
    List.map
      (fun (pat,expr) ->
         type_clause tyenv env (pat, discriminant_ty) (expr, return_ty))
      clauses
  in
  {Rewrite. f ; parameters; return_ty; discriminant; discriminant_ty; clauses}
