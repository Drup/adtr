type 'a ineq =
  | Eq of ('a Index.index * 'a Index.index)
  | Leq of ('a Index.index * 'a Index.index)

type 'a t =
  | True
  | False
  | Constr of 'a ineq
  | And of 'a t list
  | Or of 'a t list

let pp_ineq fmt = function
  | Eq (i1, i2) -> Fmt.pf fmt "%a = %a" Index.pp i1 Index.pp i2
  | Leq (i1, i2) -> Fmt.pf fmt "%a ≤ %a" Index.pp i1 Index.pp i2

let rec pp fmt = function
  | True -> Fmt.pf fmt "true"
  | False -> Fmt.pf fmt "false"
  | Constr ineq -> pp_ineq fmt ineq
  | And l -> Fmt.list ~sep:(Fmt.any " ∧@ ") pp_paren fmt l
  | Or l -> Fmt.list ~sep:(Fmt.any " ∨@ ") pp_paren fmt l
and pp_paren fmt = function
  | True | False as c -> pp fmt c
  | c -> Fmt.parens pp fmt c

let tt = True
let ff = False

let (===) (x1 : _ Index.index) (x2 : _ Index.index) =
  match x1, x2 with
  | x1, x2 when x1 = x2 -> tt
  | {constant = i1; monomes = []}, {constant = i2; monomes = []} ->
    if i1 = i2 then tt else ff
  | x1, x2 ->
    let i1 = Index.min x1 and i2 = Index.min x2 in
    let c = Index.const (- (min i1 i2)) in
    Constr (Eq Index.(x1 + c, x2 + c))

let (==<) (x1 : _ Index.index) (x2 : _ Index.index) =
  match x1, x2 with
  | x1, x2 when x1 = x2 -> tt
  | {constant = i1; monomes = []}, {constant = i2; monomes = []} ->
    if i1 <= i2 then tt else ff
  | x1, x2 ->
    let i1 = Index.min x1 and i2 = Index.min x2 in
    let c = Index.const (- (min i1 i2)) in
    Constr (Leq Index.(x1 + c, x2 + c))

let uniq l = CCList.uniq ~eq:(=) l

let mk_or l = match uniq l with
  | [] -> False
  | [x] -> x
  | l -> Or l
let mk_and l = match uniq l with
  | [] -> True
  | [x] -> x
  | l -> And l

let (|||) x1 x2 = match x1, x2 with
  | True, x | x, True -> True
  | False, x | x, False -> x
  | Or l1, Or l2 -> mk_or (l1 @ l2)
  | Or l, x | x, Or l -> mk_or (x :: l)
  | x1, x2 -> mk_or [x1;x2]
let (&&&) x1 x2 = match x1, x2 with
  | False, x | x, False -> False
  | True, x | x, True -> x
  | And l1, And l2 -> mk_and (l1 @ l2)
  | And l, x | x, And l -> mk_and (x :: l)
  | x1, x2 -> mk_and [x1;x2]

let and_ l = List.fold_left (&&&) tt l
let or_ l = List.fold_left (|||) ff l


let rec present v = function
  | Constr (Leq (i1, i2)) 
  | Constr (Eq (i1, i2)) ->
    Index.present v i1 && Index.present v i2
  | True
  | False
    -> false
  | Or l | And l ->
    List.exists (present v) l
    
let rec eval v = function
  | Constr (Eq (i1, i2)) ->
    let is_v i = Index.(is_zero @@ i1 - var v) in
    if is_v i1 then
      Index.is_constant i2
    else if is_v i2 then
      Index.is_constant i1
    else
      None
  | True
  | False
  | Constr (Leq _)
    -> None
  | Or l ->
    List.map (eval v) l
    |> CCList.uniq ~eq:CCEqual.(option int)
    |> begin function
      | [Some n] -> Some n
      | _ -> None
    end
  | And l ->
    List.filter_map (eval v) l
    |> CCList.uniq ~eq:CCInt.equal
    |> begin function
      | [n] -> Some n
      | _ -> None
    end

let rec subst v n = function
  | Constr (Eq (i1, i2)) ->
    Index.subst v n i1 === Index.subst v n i2
  | Constr (Leq (i1, i2)) ->
    Index.subst v n i1 ==< Index.subst v n i2
  | True | False as f -> f
  | And l ->
    and_ @@ List.map (subst v n) l
  | Or l ->
    or_ @@ List.map (subst v n) l

let with_dummy_var mk =
  let v = Name.fresh "dummy" in
  let f = mk v in
  match eval v f with
  | None ->
    if present v f then
      invalid_arg "Couldn't erase dummy var"
    else
      f
  | Some n ->
    subst v n f
