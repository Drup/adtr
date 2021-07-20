type var = Name.t 

type 'a monome = Name.t * 'a
type 'a index = {
  monomes : 'a monome list ;
  constant : 'a ;
}
type t = int index


let refresh_name p =
  let monomes =
    List.map (fun (var,f) -> (Name.refresh var, f)) p.monomes
  in 
  { p with monomes }

let vars x = List.map fst x.monomes |> Name.Set.of_list

let map_of_monomes l =
  Name.Map.of_list l
let monomes_of_map m =
  Name.Map.to_list m


let map_factors f { monomes; constant } =
  let constant = f constant in
  let monomes = List.map (fun (var, fact) -> (var, f fact)) monomes in
  {constant;monomes}

let on_constant f { monomes; constant } =
  let constant = f constant in
  {constant;monomes}

let map2 f e1 e2 =
  let constant = f e1.constant e2.constant in
  let monomes =
    monomes_of_map @@
    Name.Map.union (fun _ i1 i2 -> Some (f i1 i2))
    (map_of_monomes e1.monomes)
    (map_of_monomes e2.monomes)
  in
  {constant;monomes}

let eval f { monomes; constant } =
  List.fold_left (fun r (n,k) -> f n * k + r) constant monomes

let plus e1 e2 = map2 (+) e1 e2

let const constant = { monomes = [] ; constant }
let zero = const 0
let sum l = List.fold_left plus zero l

let mult k e =
  if k = 0 then const 0
  else map_factors (fun x -> k * x) e

let ( * ) k v = if k = 0 then const 0 else { monomes = [v, k] ; constant = 0 }
let ( + ) = plus
let ( *@ ) = mult
let (~- ) x = -1 *@ x
let ( - ) x1 x2 = x1 + (- x2) 

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
    Fmt.pf fmt "%a" Fmt.(hbox @@ list ~sep:(unit " +@ ") pp_monome) monomes;
    if constant = 0 then ()
    else Fmt.pf fmt " + %i" constant

let pp_parens fmt x = if need_parens x then Fmt.parens pp fmt x else pp fmt x
