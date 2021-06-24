type mult_field = {
  index : Index.t ;
  mov : Field.t ;
  suffix : Field.t ;
}

and t = [] | (::) of Field.t * mult
and mult = [] | (::) of mult_field option * layers
and layers = [] | (::) of Index.t * stop
and stop = []

let empty : t = []
let down ty pos : t = [{Field. ty; pos}] :: []
let of_fields : Field.t -> t = fun l -> [l]

let simplify (p : t) =
  let count_times_prefix_and_split ~prefix l =
    let rec take_prefix previous_rest curr_prefix l = match curr_prefix, l with
      | List.[], List.[] -> 1, List.[]
      | _, [] -> 0, previous_rest
      | [], rest ->
        let n, rest = take_prefix rest prefix rest in
        n+1, rest
      | h :: t, h' :: t' ->
        if h = h' then take_prefix previous_rest t t' else 0, previous_rest
    in
    take_prefix l prefix l
  in
  match p with
  | [] | [ [] ] | [ [] ; None ] -> []
  | [ fields ] | [ fields ; None ] -> [ fields ]
  | _ :: None :: _ as l -> l
  | before :: Some { index; mov; suffix } :: after ->
    let i, before =
      count_times_prefix_and_split ~prefix:(List.rev mov) (List.rev before)
    in
    let j, suffix =
      count_times_prefix_and_split ~prefix:mov suffix
    in
    let index = Index.(index + const i + const j) in
    List.rev before :: Some { index ; mov ; suffix } :: after

(* let rec overlap (p1:t) (p2:t) = match p1, p2 with
 *   | [], [] -> true
 *   | (`Down _ | `Any _) :: _, []
 *   | [], (`Down _ | `Any _) :: _ -> false
 *   | `Multiple _p1 :: t1, `Multiple _p2 :: t2 ->
 *     overlap t1 t2
 *   | `Any _::t1, _::t2 | _::t1, `Any _::t2 ->
 *     overlap t1 t2
 *   | (`Down x1)::t1, (`Down x2)::t2 ->
 *     x1 = x2 && overlap t1 t2
 *   | `Multiple (_,rep1) :: t1, p2 ->
 *     overlap t1 p2 (\* || 
 *                    * begin match conflict rep1 p2 with
 *                    *   | None -> false
 *                    *   | _ -> overlap (rep1 @ p1) p2
 *                    * end *\)
 *   | p1, `Multiple (_,rep2) :: t2 ->
 *     overlap p1 t2(\*  || 
 *                   * begin match conflict p1 rep2 with
 *                   *   | None -> false
 *                   *   | _ -> overlap p1 (rep2 @ p2)
 *                   * end *\) *)


let rec pp fmt (c: t) = match c with
  | [] -> Fmt.pf fmt "[]"
  | f :: t -> Field.pp fmt f; pp_mult fmt t
and pp_mult fmt = function
  | [] -> ()
  | None :: t ->
    pp_layer fmt t
  | Some { index; mov; suffix } :: t ->
    begin match mov with
      | [_] -> Fmt.pf fmt "%a^%a" Field.pp mov Index.pp_parens index
      | _ -> Fmt.pf fmt "(%a)^%a" Field.pp mov Index.pp_parens index
    end;
    Field.pp fmt suffix;
    pp_layer fmt t
and pp_layer fmt = function
  | [] -> ()
  | index :: [] ->
    Fmt.pf fmt ".φ^%a" Index.pp_parens index
