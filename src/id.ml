module M = struct
  type state = Global | Local | Left | Right
  
  type t = {
    name : string ;
    id : int ;
    state : state ;
  }

  let hash = Hashtbl.hash
  let equal n1 n2 =
    CCInt.equal n1.id n2.id &&
    CCString.equal n1.name n2.name &&
    n1.state = n2.state
  let compare n1 n2 =
    CCOrd.(int n1.id n2.id
           <?> (string, n1.name, n2.name)
           <?> (poly, n1.state, n2.state) )
end
include M

let name x = x.name

let make =
  let r = Hashtbl.create 17 in
  fun ~state s ->
    let id = CCHashtbl.get_or r s ~default:0 in
    CCHashtbl.incr r s; { name = s ; id ; state }
let global = make ~state:Global
let fresh = make ~state:Local
let freshf fmt = Fmt.kstr fresh fmt

let as_left n =
  if n.state = Local then { n with state = Left } else n

let as_right n =
  if n.state = Local then { n with state = Right } else n

let derive fmt n =
  Fmt.kstr fresh fmt n.name

let indice_array = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|]
let rec digits fmt i =
  if i < 0 then
    Format.pp_print_string fmt "₋"
  else if i < 10 then
    Format.pp_print_string fmt indice_array.(i)
  else begin
    digits fmt (i/10) ;
    Format.pp_print_string fmt indice_array.(i mod 10)
  end
let pp fmt { name ; id ; state } =
  let s = match state with
    | Global -> "!"
    | Local -> ""
    | Left -> "ˡ"
    | Right -> "ʳ"
  in
  Fmt.pf fmt "%s%s%a" name s digits id
let to_string = Fmt.to_to_string pp

module Map = CCMap.Make(M)
module Set = CCSet.Make(M)
module H = CCHashtbl.Make(M)
