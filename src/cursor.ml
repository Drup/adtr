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

let rec pp fmt (c: [< op] list) = match c with
  | [] -> ()
  | `Up :: t -> Fmt.pf fmt "↑"; pp fmt t
  | `Field i :: t -> Fmt.pf fmt ".%i" i; pp fmt t
