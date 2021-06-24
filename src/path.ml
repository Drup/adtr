type mult_field = {
  index : Index.t ;
  mov : Field.t ;
  suffix : Field.t ;
}

and t = [] | (::) of Field.t * mult
and mult = [] | (::) of mult_field option * layers
and layers = [] | (::) of Index.t * stop
and stop = []

type path = t

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



let rec pp fmt (c: path) = match c with
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


module Constr = struct
  type t =
    | True
    | False
    | Constr of (Index.t * Index.t)
    | And of t list
    | Or of t list
  let (===) x1 x2 = Constr (x1,x2)
  let tt = True
  let ff = False
  let (|||) x1 x2 = Or [x1;x2]
  let (&&&) x1 x2 = And [x1;x2]
end
open Constr

let len l = Index.const @@ List.length l
let len_layer : layers -> _ =
  function [] -> Index.const 0 | [index] -> index

let index_nullable idx =
  if Index.is_nullable idx then
    idx === Index.const 0
  else
    ff

let is_nullable = function
  | [] | [[]] | [ [] ; None ] -> tt
  | _ :: Some { index ; mov = _ ; suffix = [] } :: [] ->
    index_nullable index
  | _ :: Some { index ; mov = _ ; suffix = [] } :: index2 :: [] ->
    let index' = Index.plus index index2 in
    index_nullable index'
  | _ :: None :: index2 :: [] ->
    index_nullable index2
  | (_::_) :: _
  | _ :: Some { suffix = (_::_) } :: _
    -> ff

let rec overlap (p1:path) (p2:path) = match p1, p2 with
  (* Both are empty *)
  | ([] | [[]] | [ [] ; None ]),
    ([] | [[]] | [ [] ; None ]) -> tt
  (* One of them is empty *)
  | l, ([] | [[]] | [ [] ; None ])
  | ([] | [[]] | [ [] ; None ]), l
    -> is_nullable l
  (* Without multiple, but potentially with wildcards *)
  | l1::None::rest1 , l2::None::rest2 -> overlap_no_mult (l1,rest1) (l2, rest2)
  | l1::None::rest1 , l2::[]          -> overlap_no_mult (l1,rest1) (l2, [])
  | l1::[]          , l2::None::rest2 -> overlap_no_mult (l1,[]) (l2, rest2)
  | l1::[]          , l2::[]          -> overlap_no_mult (l1,[]) (l2, [])
  (* With multiple on one side *)
  | l1::Some mult1 :: rest1, l2 :: None :: rest2
  | l2 :: None :: rest2, l1::Some mult1 :: rest1
    -> overlap_one_mult (l1, mult1, rest1) (l2,rest2)
  | l1::Some mult1 :: rest1, l2 :: []
  | l2 :: [], l1::Some mult1 :: rest1
    -> overlap_one_mult (l1, mult1, rest1) (l2,[])
  (* With multiple on both side *)
  | l1::(Some mult1)::wild1, l2::(Some mult2)::wild2 ->
    match Field.conflict l1 l2 with
    | None -> ff
    | Some ((`eq|`left), m) ->
      overlap_two_mult (m,mult2,wild2) (mult1, wild1)
    | Some (`right, m) ->
      overlap_two_mult (m,mult1,wild1) (mult2, wild2)

and overlap_no_mult (prefix1,wild1) (prefix2,wild2) =
  match Field.conflict prefix1 prefix2 with
  | None -> ff
  | Some _ -> 
    Index.(
      len_layer wild1 + len prefix1 === len_layer wild2 + len prefix2
    )

and overlap_one_mult (prefix1,{ index; mov; suffix },wild1) (prefix2,wild2) =
  match Field.conflict prefix1 prefix2 with
  | None -> ff
  | Some (`eq, _) ->
    Index.(
      (len mov * index) + len suffix + len_layer wild1 ===
      len_layer wild2
    )
  | Some (`right, m) ->
    Index.(
      len m + (len mov * index) + len suffix + len_layer wild1 ===
      len_layer wild2
    )
  | Some (`left, m) ->
    let b1 =
      (index === Index.const 0) &&&
      overlap_no_mult (suffix, wild1) (m, wild2)
    and b2 =
      overlap_one_mult
        (mov, {index = Index.decr index;mov;suffix}, wild1)
        (m, wild2)
    in
    b1 ||| b2

and overlap_two_mult (prefix1, mult1, wild1) (mult2, wild2) =
  assert false
