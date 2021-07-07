type t =
  | True
  | False
  | Constr of (Index.t * Index.t)
  | And of t list
  | Or of t list

let tt = True
let ff = False
  
let (===) (x1 : Index.t) (x2 : Index.t) =
  match x1, x2 with
  | x1, x2 when x1 = x2 -> tt
  | {constant = i1; monomes = []}, {constant = i2; monomes = []} ->
    if i1 = i2 then tt else ff
  | x1, x2 -> 
    let i1 = Index.min x1 and i2 = Index.min x2 in
    let c = Index.const (- (min i1 i2)) in
    Constr Index.(x1 + c, x2 + c)

let (|||) x1 x2 = match x1, x2 with
  | True, x | x, True -> True
  | False, x | x, False -> x
  | Or l1, Or l2 -> Or (l1 @ l2)
  | Or l, x | x, Or l -> Or (x :: l)
  | x1, x2 -> Or [x1;x2]
let (&&&) x1 x2 = match x1, x2 with
  | False, x | x, False -> False
  | True, x | x, True -> x
  | And l1, And l2 -> And (l1 @ l2)
  | And l, x | x, And l -> And (x :: l)
  | x1, x2 -> And [x1;x2]

let rec pp fmt = function
  | True -> Fmt.pf fmt "true"
  | False -> Fmt.pf fmt "false"
  | Constr (i1, i2) -> Fmt.pf fmt "%a = %a" Index.pp i1 Index.pp i2
  | And l -> Fmt.list ~sep:(Fmt.unit " ∧@ ") pp_paren fmt l
  | Or l -> Fmt.list ~sep:(Fmt.unit " ∨@ ") pp_paren fmt l
and pp_paren fmt = function
  | True | False as c -> pp fmt c
  | c -> Fmt.parens pp fmt c
