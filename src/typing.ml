open Syntax

type error =
  | Overlapping_name of Name.t
  | Unbound_variable of Name.t
  | Cannot_pattern_match of Syntax.type_expr
  | Not_a_function of Name.t * Syntax.type_expr
  | Arity_dont_match of Name.t * Syntax.type_expr * int
  | Types_dont_match of Syntax.type_expr * Syntax.type_expr
  | Constructor_not_allowed of Name.t
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
  | Error (Arity_dont_match (name,ty,i)) ->
    Some
      (Report.errorf "The function %a has type %a. It is applied to %i arguments."
         Name.pp name Printer.types ty i)
  | Error (Not_a_function (n, ty)) ->
    Some
      (Report.errorf "The variable %a has type %a. It is not a function. It cannot be applied."
         Name.pp n Printer.types ty)
  | Error (Constructor_not_allowed str) ->
    Some
      (Report.errorf "This is a the type constructor %a. Type constructors are not allowed in this position"
         Name.pp str)
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
      register_name name (pat_ty, Rewrite.Position (Some name, path)) posmap
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

let rec type_expression tyenv env posmap (path : Field.t) expr0 expr_ty0 =
  match expr0 with
  | EApp _ | EVar _ as expr ->
    let name =
      match expr with EVar n -> n | EApp (n,_) -> Name.fresh n | _ -> assert false
    in
    let dest = Some path in
    let src = type_hole tyenv env expr expr_ty0 in
    let ty = expr_ty0 in
    {Rewrite. name ; src; dest ; ty } :: posmap
  | EConstructor { constructor; arguments } ->
    let argument_tys =
      Types.instantiate_data_constructor tyenv constructor expr_ty0
    in
    CCList.foldi2
      (fun posmap pos expr expr_ty ->
         type_expression tyenv env posmap
           Field.(path +/ { ty = expr_ty; pos}) expr expr_ty)
      posmap arguments argument_tys

and type_hole tyenv env expr expr_ty = match expr with
  | EVar name ->
    let ty, src_pos = get_name name env in
    check ty expr_ty;
    Rewrite.Slot src_pos
  | EApp (name, args) ->
    let ty, src_pos = get_name name env in
    begin match ty with
      | TFun (params, ret) -> 
        check ret expr_ty;
        if List.length params <> List.length args then
          error @@ Arity_dont_match (name, ty, List.length args)
        else
          let l = List.map2 (type_hole tyenv env) args params in
          Rewrite.App (name, l)
      | _ ->
        error @@ Not_a_function (name, ty)
    end
  | EConstructor { constructor; _ } ->
    error @@ Constructor_not_allowed constructor

let type_clause tyenv env (pattern, pat_ty) (expr, expr_ty) =
  let inputs = Name.Map.mapi (fun n ty -> ty, Rewrite.External n) env in
  let srcs = type_pattern tyenv inputs pattern pat_ty in
  let env =
    Name.Map.union (fun _ _ e -> Some e) inputs srcs
  in
  let dests = type_expression tyenv env [] Field.empty expr expr_ty in
  dests
  (* This sorting is only for convenience and test stability *)
  |> List.sort (fun a b -> Stdlib.compare a.Rewrite.name b.name)


let (-->) l t = TFun (l, t)
let init = Name.Map.of_list [
    "+", [ TInt; TInt ] --> TInt;
    "*", [ TInt; TInt ] --> TInt;
    "/", [ TInt; TInt ] --> TInt;
    "-", [ TInt; TInt ] --> TInt;
  ]

let type_rewrite
    tyenv {Syntax. f ; parameters ; return_ty ; discriminant ; clauses } =
  let env =
    List.fold_left
      (fun e (n,ty) -> register_name n ty e)
      init parameters
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
