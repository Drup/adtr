open Syntax

type error =
  | Unbound_type of Name.t
  | Unbound_type_variable of Name.t
  | Bad_constructor of name * Syntax.type_expr
exception Error of error
let error e = raise @@ Error e

let rec pp fmt ty = match ty with
  | TInt -> Fmt.pf fmt "int"
  | TVar name -> Fmt.pf fmt "'%a" Name.pp name
  | TConstructor {constructor; arguments = []} ->
    Fmt.pf fmt "%a" Name.pp constructor
  | TConstructor {constructor; arguments} ->
    Fmt.pf fmt "%a (%a)"
      Name.pp constructor
      (Fmt.list ~sep:Fmt.comma pp) arguments

let prepare_error = function
  | Error (Unbound_type_variable n) -> 
    Some (Report.errorf "The type variable %a is unbounded" Name.pp n)
  | Error (Unbound_type n) -> 
    Some (Report.errorf "The type constructor %a is unbounded" Name.pp n)
  | Error (Bad_constructor (n, ty)) ->
    Some
      (Report.errorf "The data constructor %a doesn't belong to the type %a."
         Name.pp n pp ty)
  | _ -> None

let () =
  Report.register_report_of_exn prepare_error

let is_scalar ty = match ty with
  | TInt -> true
  | TConstructor _ -> false
  | TVar _ -> assert false

module Env = struct

  type t = Syntax.type_declaration Name.Map.t

  let empty = Name.Map.empty

  let add = Name.Map.add

  let get n e : type_declaration =
    match Name.Map.get n e with
    | None -> error @@ Unbound_type n
    | Some v -> v
end

module Subst = struct

  type t = type_expr Name.Map.t

  let empty = Name.Map.empty

  let var subst n =
    match Name.Map.get n subst with
    | None -> error @@ Unbound_type_variable n
    | Some v -> v

  let rec type_expr subst ty =
    match ty with
    | TVar n -> var subst n
    | TInt -> TInt
    | TConstructor { constructor; arguments } ->
      let arguments = List.map (type_expr subst) arguments in
      TConstructor { constructor; arguments }

end

let rec instantiate_data_constructor_with_subst tyenv subst constructor ty =
  match ty with
  | TVar name ->
    let ty = Subst.var subst name in
    instantiate_data_constructor_with_subst tyenv subst constructor ty
  | TInt -> error @@ Bad_constructor (constructor, ty)
  | TConstructor { constructor = type_name ; arguments } ->
    let { name = _ ; parameters ; definition } = Env.get type_name tyenv in
    let subst =
      let f e name ty = Name.Map.add name ty e in
      List.fold_left2 f subst parameters arguments
    in
    begin
      match definition with
      | Sum constrs ->
        match CCList.find_opt (fun x -> x.constructor = constructor) constrs with
        | None -> error @@ Bad_constructor (constructor, ty)
        | Some { constructor = _ ; arguments } ->
          List.map (Subst.type_expr subst) arguments
    end

let instantiate_data_constructor tyenv constructor ty =
  instantiate_data_constructor_with_subst tyenv Subst.empty constructor ty
