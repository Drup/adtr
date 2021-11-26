open Syntax

let rec types fmt ty = match ty with
  | TInt -> Fmt.pf fmt "int"
  | TVar name -> Fmt.pf fmt "'%s" name
  | TConstructor {constructor; arguments = []} ->
    Fmt.pf fmt "%s" constructor
  | TFun ([args], ret) ->
    Fmt.pf fmt "%a -> %a"
      types args
      types ret
  | TFun (args, ret) ->
    Fmt.pf fmt "(%a) -> %a"
      (Fmt.list ~sep:Fmt.comma types) args
      types ret
  | TConstructor {constructor; arguments} ->
    Fmt.pf fmt "%s (%a)"
      constructor
      (Fmt.list ~sep:Fmt.comma types) arguments

let constant fmt = function
  | Int i -> Fmt.int fmt i
