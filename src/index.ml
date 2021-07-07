type t =
  | Var of Name.t
  | Constant of int
  | Sum of t list
  | Product of t list

let rec refresh_name = function
  | Var n -> Var (n ^"'")
  | Constant i -> Constant i
  | Sum l -> Sum (List.map refresh_name l)
  | Product l -> Product (List.map refresh_name l)

let rec simplify = function
  | Var _ 
  | Constant _ as e -> e
  | Sum l -> sum l
  | Product l -> product l

and sum l0 = 
  let rec aux ~constant ~others = function
    | [] ->
      begin match others, constant with
        | [], c -> Constant c
        | [e], 0 -> e
        | l, 0 -> Sum l
        | l, c -> Sum (l @ [Constant c])
      end
    | h :: t ->
      begin match simplify h with
        | Var _ | Product _ as e ->
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

and product l0 = 
  let rec aux ~constant ~others = function
    | [] ->
      if constant = 1 then
        begin match others with
          | [] -> Constant constant
          | [e] -> e
          | l -> Product l
        end
      else
        Product (others @ [Constant constant])
    | h :: t ->
      begin match simplify h with
        | Var _ | Sum _ as e ->
          let others = e :: others in
          aux ~constant ~others t
        | Constant i ->
          let constant = constant * i in
          aux ~constant ~others t
        | Product inner ->
          aux ~constant ~others (inner @ t)          
      end
  in
  aux ~constant:1 ~others:[] l0

let var n = Var n
let const i = Constant i
let plus a b = sum [a;b]
let (+) = plus
let mult a b = product [a;b]
let ( * ) = mult
let incr x = x + Constant 1
let decr x = x + Constant (-1)

let rec is_nullable = function
  | Var _ -> true
  | Constant i -> i = 0
  | Sum l -> List.for_all is_nullable l
  | Product l -> List.exists is_nullable l

let need_parens = function
  | Var _ | Constant _ -> false
  | Sum _ | Product _ -> true

let rec pp fmt = function
  | Var n -> Name.pp fmt n
  | Constant i -> Fmt.int fmt i
  | Sum l ->
    Fmt.(hbox @@ list ~sep:(unit "@ + ") pp_parens) fmt l
  | Product l ->
    Fmt.(hbox @@ list ~sep:(unit "@ * ") pp_parens) fmt l
and pp_parens fmt x = if need_parens x then Fmt.parens pp fmt x else pp fmt x
    
