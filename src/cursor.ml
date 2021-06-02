type down = [
  | `Field of int
]

type op = [
  | `Up
  | down
]

type path = down list
type cursor = op list

let rec simplify : cursor -> cursor = function
  | `Field _ :: `Up :: l -> simplify l
  | h :: t -> h :: simplify t
  | [] -> []
let (++) a b = simplify @@ List.append a b

let up = `Up
let field i = `Field i
let empty = []

let rec invert : path -> cursor = List.map (function `Field _ -> `Up)
let movement p1 p2 =
    invert p1 ++ p2

let rec conflict (p1:path) (p2:path) = match p1, p2 with
  | [], l -> Some (List.length l) 
  | l, [] -> Some (- (List.length l))
  | h1::t1, h2::t2 when h1 = h2 -> conflict t1 t2
  | _ -> None

let rec pp fmt (c: [< op] list) = match c with
  | [] -> ()
  | `Up :: t -> Fmt.pf fmt "↑"; pp fmt t
  | `Field i :: t -> Fmt.pf fmt ".%i" i; pp fmt t
