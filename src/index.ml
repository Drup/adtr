type var = Id.t 

type 'a monome = Id.t * 'a
type 'a index = {
  monomes : 'a monome list ;
  constant : 'a ;
}
type t = int index


let map_vars f { monomes; constant } =
  let monomes =
    List.map (fun (var,k) -> (f var, k)) monomes
  in 
  { monomes ; constant }

let vars x = List.map fst x.monomes |> Id.Set.of_list

let map_of_monomes l =
  Id.Map.of_list l
let monomes_of_map m =
  Id.Map.to_list m


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
    Id.Map.union (fun _ i1 i2 -> Some (f i1 i2))
    (map_of_monomes e1.monomes)
    (map_of_monomes e2.monomes)
  in
  {constant;monomes}

let eval f { monomes; constant } =
  List.fold_left (fun r (n,k) -> f n * k + r) constant monomes

let present v { monomes; constant = _ } =
  CCList.Assoc.mem ~eq:Id.equal v monomes

let subst v n { monomes; constant } =
  match CCList.Assoc.get ~eq:Id.equal v monomes with
  | None -> { monomes; constant }
  | Some k -> 
    let monomes = CCList.Assoc.remove ~eq:Id.equal v monomes in
    let constant = constant + k * n in
    { monomes; constant }

let simplify { monomes ; constant } =
  let monomes = List.filter (fun (_,i) -> i <> 0) monomes in
  { monomes ; constant }

let plus e1 e2 = simplify @@ map2 (+) e1 e2

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

let is_constant e = match simplify e with
  | { monomes = [] ; constant } -> Some constant
  | _ -> None
let is_zero e = is_constant e = Some 0
                      
let need_parens = function
  | { constant = 0 ; monomes = [_] }
  | { monomes = []; _} -> false
  | _ -> true

let pp_monome fmt (var,k) =
  if k = 1 then Id.pp fmt var else Fmt.pf fmt "%i*%a" k Id.pp var 
let pp fmt { constant ; monomes } =
  match constant, monomes with
  | i, [] -> Fmt.int fmt i
  | i, l ->
    Fmt.pf fmt "%a" Fmt.(hbox @@ list ~sep:(any " +@ ") pp_monome) monomes;
    if constant = 0 then ()
    else Fmt.pf fmt " + %i" constant

let pp_parens fmt x = if need_parens x then Fmt.parens pp fmt x else pp fmt x
