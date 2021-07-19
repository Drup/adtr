open Syntax

let rec types fmt ty = match ty with
  | TInt -> Fmt.pf fmt "int"
  | TVar name -> Fmt.pf fmt "'%a" Name.pp name
  | TConstructor {constructor; arguments = []} ->
    Fmt.pf fmt "%a" Name.pp constructor
  | TFun ([args], ret) ->
    Fmt.pf fmt "%a -> %a"
      types args
      types ret
  | TFun (args, ret) ->
    Fmt.pf fmt "(%a) -> %a"
      (Fmt.list ~sep:Fmt.comma types) args
      types ret
  | TConstructor {constructor; arguments} ->
    Fmt.pf fmt "%a (%a)"
      Name.pp constructor
      (Fmt.list ~sep:Fmt.comma types) arguments
