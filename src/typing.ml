open Syntax

type error =
  | Overlapping_name of Name.t
  | Unbound_variable of Name.t
  | Cannot_pattern_match of Syntax.type_expr
  | Types_dont_match of Syntax.type_expr * Syntax.type_expr
exception Error of error
let error e = raise @@ Error e

let prepare_error = function
  | Error (Overlapping_name n) ->
    Some
      (Report.errorf "This variable `%a` is defined twice in this clause. This is not allowed." Name.pp n)
  | Error (Unbound_variable n) -> 
    Some
      (Report.errorf "The variable %a is unbounded" Name.pp n)
  | Error (Cannot_pattern_match ty) ->
    Some
      (Report.errorf "This rewrite is applied to a value of type %a.@ Values of this type can't be rewriten." Printer.types ty)
  | Error (Types_dont_match (ty1,ty2)) ->
    Some
      (Report.errorf "The type %a was expected, but we got type %a"
         Printer.types ty2 Printer.types ty1)
  | _ -> None

let () =
  Report.register_report_of_exn prepare_error


let register_name n t e =
  if Name.Map.mem n e then
    error @@ Overlapping_name n
  else
    Name.Map.add n t e
let add_name n t e =
  Name.Map.update n (function
      | None -> Some [t]
      | Some l -> Some (t :: l))
    e
let get_name n e =
  match Name.Map.get n e with
  | None -> error @@ Unbound_variable n
  | Some v -> v

let check ty1 ty2 =
  if Types.equal ty1 ty2 then () else error @@ Types_dont_match (ty1, ty2)

let type_pattern tyenv posmap0 pattern0 pat_ty0 = 
  let rec aux posmap (path : Field.t) pattern pat_ty = match pattern with
    | PVar name ->
      register_name name (Rewrite.Internal path, pat_ty) posmap
    | PConstructor { constructor; arguments } ->
      let argument_tys =
        Types.instantiate_data_constructor tyenv constructor pat_ty
      in
      CCList.foldi2
        (fun env pos pattern pat_ty ->
           aux env Field.(path +/ {ty = pat_ty; pos}) pattern pat_ty)
        posmap arguments argument_tys
  in
  aux posmap0 Field.empty pattern0 pat_ty0

let env_of_posmap posmap = Name.Map.map snd posmap

let type_expression tyenv env posmap0 expr0 expr_ty0 = 
  let rec aux posmap (path : Field.t) expr expr_ty = match expr with
    | EVar name ->
      let ty = get_name name env in
      check ty expr_ty;
      add_name name (Rewrite.Internal path) posmap
    | EConstructor { constructor; arguments } ->
      let argument_tys =
        Types.instantiate_data_constructor tyenv constructor expr_ty
      in
      CCList.foldi2
        (fun env pos expr expr_ty ->
           aux env Field.(path +/ { ty = expr_ty; pos}) expr expr_ty)
        posmap arguments argument_tys
  in
  aux posmap0 Field.empty expr0 expr_ty0

let type_clause tyenv env (pattern, pat_ty) (expr, expr_ty) =
  let inputs = Name.Map.map (fun ty -> Rewrite.External, ty) env in
  let srcs = type_pattern tyenv inputs pattern pat_ty in
  let env =
    Name.Map.union (fun _ _ e -> Some e) env (env_of_posmap srcs)
  in
  let dests = type_expression tyenv env Name.Map.empty expr expr_ty in
  Name.Map.fold 
    ((fun name (src, ty) rules ->
        match Name.Map.get name dests with
        | None ->
          {Rewrite. name ; src; dest = Absent ; ty } :: rules
        | Some dests ->
          List.map (fun dest -> {Rewrite. name ; src; dest; ty }) dests
          @ rules
      ))
    srcs []
  (* This sorting is only for convenience and test stability *)
  |> List.sort (fun a b -> Stdlib.compare a.Rewrite.name b.name)

let type_rewrite
    tyenv {Syntax. f ; parameters ; return_ty ; discriminant ; clauses } =
  let env =
    List.fold_left
      (fun e (n,ty) -> register_name n ty e)
      Name.Map.empty parameters
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
