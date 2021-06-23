type field = [
  | `Down of Syntax.type_expr * int
]
type fields = field list

type down = [
  | `Down of Syntax.type_expr * int
  | `Multiple of Index.t * fields
]
and path = down list

let (+/) : fields -> field -> fields = fun a b -> a @ [b]

let rec simplify : ([< down] list as 'a) -> 'a = function
  | h :: t -> h :: simplify t
  | [] -> []
let (++) a b = simplify @@ List.append a b

let down constr i = `Down (constr, i)
let empty = []

let as_path x = (x :> path)

(** [conflict p1 p2] computes if one path is prefix of the other.
    Return which one is shortest, along with the extra bits *)
let rec conflict (p1:fields) (p2:fields) = match p1, p2 with
  | [], l -> Some (`left, l)
  | l, [] -> Some (`right, l)
  | (`Down x1)::t1, (`Down x2)::t2 ->
    if x1 = x2 then conflict t1 t2
    else None


let rec overlap (p1:path) (p2:path) = match p1, p2 with
  | [], [] -> true
  | `Down _ :: _, []
  | [], `Down _ :: _ -> false
  | `Multiple _p1 :: t1, `Multiple _p2 :: t2 ->
    overlap t1 t2
  | (`Down x1)::t1, (`Down x2)::t2 ->
    x1 = x2 && overlap t1 t2
  | `Multiple (_,rep1) :: t1, p2 ->
    overlap t1 p2 (* || 
     * begin match conflict rep1 p2 with
     *   | None -> false
     *   | _ -> overlap (rep1 @ p1) p2
     * end *)
  | p1, `Multiple (_,rep2) :: t2 ->
    overlap p1 t2(*  || 
     * begin match conflict p1 rep2 with
     *   | None -> false
     *   | _ -> overlap p1 (rep2 @ p2)
     * end *)

let rec pp_path fmt (c: path) = match c with
  | [] -> ()
  | `Down (constr,i) :: t -> Fmt.pf fmt ".%a@%i" Types.pp constr i; pp_path fmt t
  | `Multiple (i, ([_] as path)) :: t ->
    Fmt.pf fmt "%a^%a" pp_path (path :> path) Index.pp_parens i; pp_path fmt t
  | `Multiple (i, path) :: t ->
    Fmt.pf fmt "(%a)^%a" pp_path (path :> path) Index.pp_parens i; pp_path fmt t

let pp_path fmt = function
  | [] -> Fmt.pf fmt "[]"
  | l -> pp_path fmt l

let pp fmt p = pp_path fmt (p : fields :> path)
