type down = [
  | `Down of Name.t * int
  | `Multiple of Index.t * path
]
and path = down list

type op = [
  | `Up of Name.t * int
  | `Down of Name.t * int
  | `Multiple of Index.t * cursor
]
and cursor = op list

let (+/) : path -> down -> path = fun a b -> a @ [b]

let rec simplify : ([< op] list as 'a) -> 'a = function
  | `Down _ :: `Up _ :: l -> simplify l
  | h :: t -> h :: simplify t
  | [] -> []
let (++) a b = simplify @@ List.append a b

let up = `Up
let down constr i = `Down (constr, i)
let empty = []

let rec invert (p : path) : cursor =
  List.map
    (function `Down f -> `Up f | `Multiple (n, p) -> `Multiple (n, invert p))
    p

let movement p1 p2 =
    invert p1 ++ p2

(** [conflict p1 p2] computes if one path is prefix of the other.
    Return which one is shortest, along with the extra bits *)
let rec conflict (p1:path) (p2:path) = match p1, p2 with
  | `Multiple _ :: [], `Multiple _ :: l
  | [], l -> Some (`left, l)
  | `Multiple _ :: l, `Multiple _ :: []
  | l, [] -> Some (`right, l)
  | `Multiple p1 :: (_ :: _ as t1), `Multiple p2 :: (_ :: _ as t2) ->
    if p1 = p2 then conflict t1 t2
    else None (* Only because t1 and t2 are both non-empty *)
  | `Multiple (_,p1) :: t1, (`Down _ :: _) ->
    begin match conflict p1 p2 with
      | None -> conflict t1 p2
      | Some (`right,_) as o -> o
      | Some (`left, extra) -> (* conflict t1 extra *) None
    end
  | (`Down _ :: _), `Multiple (_,p2) :: t2 ->
    begin match conflict p1 p2 with
      | None -> conflict p1 t2
      | Some (`left, _) as o -> o
      | Some (`right, extra) -> (* conflict extra t2 *) None
    end
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

let rec pp_cursor fmt (c: cursor) = match c with
  | [] -> ()
  | `Up (constr,i) :: t -> Fmt.pf fmt "↑%i" i; pp_cursor fmt t
  | `Down (constr,i) :: t -> Fmt.pf fmt ".%i" i; pp_cursor fmt t
  | `Multiple (i, ([_] as path)) :: t ->
    Fmt.pf fmt "%a^%a" pp_cursor path Index.pp_parens i; pp_cursor fmt t
  | `Multiple (i, path) :: t ->
    Fmt.pf fmt "(%a)^%a" pp_cursor path Index.pp_parens i; pp_cursor fmt t

let pp_cursor fmt = function
  | [] -> Fmt.pf fmt "[]"
  | l -> pp_cursor fmt l

let pp fmt p = pp_cursor fmt (p : path :> cursor)
