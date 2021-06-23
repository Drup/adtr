type t =
  | Var of Name.t
  | Constant of int
  | Sum of t list

let rec simplify = function
  | Var _ 
  | Constant _ as e -> e
  | Sum l -> sum l

and sum l0 = 
  let rec aux ~constant ~others = function
    | [] ->
      if constant = 0 then
        begin match others with
          | [e] -> e
          | l -> Sum l
        end
      else
        Sum (others @ [Constant constant])
    | h :: t ->
      begin match simplify h with
        | Var _ as e ->
          let others = e :: others in
          aux ~constant ~others t
        | Constant i ->
          let constant = constant + i in
          aux ~constant ~others t
        | Sum inner ->
          aux ~constant ~others (inner @ t)
      end
  in
  aux ~constant:0 ~others:[] l0

let var n = Var n
let const i = Constant i
let plus a b = sum [a;b]
let (+) = plus
let incr x = x + Constant 1

let need_parens = function
  | Var _ | Constant _ -> false
  | Sum _ -> true

let rec pp fmt = function
  | Var n -> Name.pp fmt n
  | Constant i -> Fmt.int fmt i
  | Sum l ->
    Fmt.(hbox @@ list ~sep:(unit "@ + ") pp_parens) fmt l
and pp_parens fmt x = if need_parens x then Fmt.parens pp fmt x else pp fmt x
    
