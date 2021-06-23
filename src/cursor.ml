type field = [
  | `Down of Syntax.type_expr * int
]
type fields = field list

let (+/) : fields -> field -> fields = fun a b -> a @ [b]
(** [conflict p1 p2] computes if one path is prefix of the other.
    Return which one is shortest, along with the extra bits *)

let rec conflict (p1:fields) (p2:fields) = match p1, p2 with
  | [], l -> Some (`left, l)
  | l, [] -> Some (`right, l)
  | (`Down x1)::t1, (`Down x2)::t2 ->
    if x1 = x2 then conflict t1 t2
    else None

type down = [
  | field
  | `Any of Index.t
  | `Multiple of Index.t * fields
]
and path = down list

let as_path x = (x :> path)

let simplify (p : path) =
  let count_times_prefix_and_split ~prefix l =
    let rec take_prefix previous_rest curr_prefix l = match curr_prefix, l with
      | [], [] -> 1, []
      | _, [] -> 0, previous_rest
      | [], rest ->
        let n, rest = take_prefix rest prefix rest in
        n+1, rest
      | h :: t, h' :: t' ->
        if h = h' then take_prefix previous_rest t t' else 0, previous_rest
    in
    take_prefix l prefix l
  in
  let rec split_at_first_multiple before_rev = function
    | [] -> `No_multiple (List.rev before_rev)
    | (`Down _ | `Any _)  as f :: after ->
      split_at_first_multiple (f :: before_rev) after
    | `Multiple _ as f :: after ->
      `Some_multiple (before_rev, f, after)
  in
  let rec merge_at_multiple (p : [< down] list) =
    match split_at_first_multiple [] p with
    | `No_multiple l ->
      as_path l
    | `Some_multiple (before_rev, `Multiple (k,l), after) ->
      let mov = as_path l in
      let i, rest_before =
        count_times_prefix_and_split ~prefix:(List.rev mov) before_rev
      in
      let j, rest_after =
        match split_at_first_multiple [] after with
        | `No_multiple after ->
          count_times_prefix_and_split ~prefix:mov after
        | `Some_multiple (after1, f, after2) ->
          let j, after1 = count_times_prefix_and_split ~prefix:mov after1 in
          j, after1 @ f :: after2
      in
      let k = Index.(k + const i + const j) in
      as_path (List.rev rest_before)
      @ [`Multiple (k,l)]
      @ merge_at_multiple rest_after
  in
  merge_at_multiple p

let (++) a b = simplify @@ List.append a b

let down constr i = `Down (constr, i)
let empty = []




let rec overlap (p1:path) (p2:path) = match p1, p2 with
  | [], [] -> true
  | (`Down _ | `Any _) :: _, []
  | [], (`Down _ | `Any _) :: _ -> false
  | `Multiple _p1 :: t1, `Multiple _p2 :: t2 ->
    overlap t1 t2
  | `Any _::t1, _::t2 | _::t1, `Any _::t2 ->
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
  | `Down (ty,i) :: t -> Fmt.pf fmt ".%a@%i" Types.pp ty i; pp_path fmt t
  | `Any k :: t -> Fmt.pf fmt ".φ^%a" Index.pp_parens k; pp_path fmt t
  | `Multiple (k, ([_] as path)) :: t ->
    Fmt.pf fmt "%a^%a" pp_path (path :> path) Index.pp_parens k; pp_path fmt t
  | `Multiple (k, path) :: t ->
    Fmt.pf fmt "(%a)^%a" pp_path (path :> path) Index.pp_parens k; pp_path fmt t

let pp_path fmt = function
  | [] -> Fmt.pf fmt "[]"
  | l -> pp_path fmt l

let pp fmt p = pp_path fmt (p : fields :> path)
