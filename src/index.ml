type var = Name.t 

type monome = Name.t * int
type t = {
  monomes : monome list ;
  constant : int ;
}

let refresh_name p =
  let monomes =
    List.map (fun (var,f) -> (var ^"'", f)) p.monomes
  in 
  { p with monomes }

let map_of_monomes l =
  Name.Map.of_list l
let monomes_of_map m =
  Name.Map.to_list m


let map_factors f { monomes; constant } =
  let constant = f constant in
  let monomes = List.map (fun (var, fact) -> (var, f fact)) monomes in
  {constant;monomes}

let plus e1 e2 =
  let constant = e1.constant + e2.constant in
  let monomes =
    monomes_of_map @@
    Name.Map.union (fun _ i1 i2 -> Some (i1 + i2))
    (map_of_monomes e1.monomes)
    (map_of_monomes e2.monomes)
  in
  {constant;monomes}

let const constant = { monomes = [] ; constant }
let zero = const 0

let mult k e =
  if k = 0 then const 0
  else map_factors (fun x -> k * x) e

let ( * ) k v = if k = 0 then const 0 else { monomes = [v, k] ; constant = 0 }
let ( + ) = plus
let ( *@ ) = mult

let var v = 1 * v

let incr x = x + (const 1)
let decr x = x + (const (-1))

let min e = e.constant
let is_nullable e = min e = 0

let need_parens = function
  | { constant = 0 ; monomes = [_] }
  | { monomes = []; _} -> false
  | _ -> true

let pp_monome fmt (var,k) =
  if k = 1 then Name.pp fmt var else Fmt.pf fmt "%i*%a" k Name.pp var 
let pp fmt { constant ; monomes } =
  match constant, monomes with
  | i, [] -> Fmt.int fmt i
  | i, l ->
    Fmt.pf fmt "%a" Fmt.(hbox @@ list ~sep:(unit " + ") pp_monome) monomes;
    if constant = 0 then ()
    else Fmt.pf fmt " + %i" constant

let pp_parens fmt x = if need_parens x then Fmt.parens pp fmt x else pp fmt x
