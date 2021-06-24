type op = [
  | `Down of Field.field
  | `Any of Index.t
  | `Multiple of Index.t * Field.t
]
and t = op list

let empty = []
let down ty pos : op = `Down {Field. ty; pos}
let any k : op = `Any k
let of_fields : Field.t -> t = List.map (fun x -> `Down x)

let simplify (p : t) =
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
  let rec merge_at_multiple (p : [< op] list) =
    match split_at_first_multiple [] p with
    | `No_multiple l ->
      l
    | `Some_multiple (before_rev, `Multiple (k,l), after) ->
      let mov = of_fields l in
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
      (List.rev rest_before)
      @ [`Multiple (k,l)]
      @ merge_at_multiple rest_after
  in
  merge_at_multiple p

let (++) a b = simplify @@ List.append a b




let rec overlap (p1:t) (p2:t) = match p1, p2 with
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


let rec pp fmt (c: t) = match c with
  | [] -> ()
  | `Down f :: t -> Field.pp_field fmt f; pp fmt t
  | `Any k :: t -> Fmt.pf fmt ".φ^%a" Index.pp_parens k; pp fmt t
  | `Multiple (k, ([_] as fields)) :: t ->
    Fmt.pf fmt "%a^%a" Field.pp fields Index.pp_parens k; pp fmt t
  | `Multiple (k, fields) :: t ->
    Fmt.pf fmt "(%a)^%a" Field.pp fields Index.pp_parens k; pp fmt t

let pp fmt = function
  | [] -> Fmt.pf fmt "[]"
  | l -> pp fmt l
