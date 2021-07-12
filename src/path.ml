type mult_field = {
  index : Index.t ;
  mov : Field.t ;
  suffix : Field.t ;
}

let equal_field l1 l2 =
  CCList.equal
    (fun (f1 : Field.field) f2 -> f1.pos = f2.pos && Types.equal f1.ty f2.ty)
    l1 l2


type t = [] | (::) of Field.t * mult
and mult = [] | (::) of mult_field option * layers
and layers = [] | (::) of Index.t * stop
and stop = []

type path = t

let vars : t -> _ = function
  | [ x ; Some { index ; _ } ; idx2 ] ->
    Name.Set.union (Index.vars index) (Index.vars idx2)
  | [ x ; Some { index ; _ } ] ->
    Index.vars index
  | [ x ; None ; idx2 ] ->
    Index.vars idx2
  | l -> Name.Set.empty

let refresh : t -> t = function
  | [ x ; Some ({ index ; _ } as mult) ; idx2 ] ->
    [ x ; Some {mult with index = Index.refresh_name index} ;
      Index.refresh_name idx2 ]
  | [ x ; Some ({ index ; _ } as mult) ] ->
    [ x ; Some {mult with index = Index.refresh_name index} ]
  | [ x ; None ; idx2 ] ->
    [ x ; None ; Index.refresh_name idx2 ]
  | l -> l

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



let rec pp fmt (c: path) = match simplify c with
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

(** Utilities for building constraint and linear forms *)

let lenf l = List.length l
let len l = Index.const @@ List.length l
let len_layer : layers -> _ =
  function [] -> Index.const 0 | [index] -> index

(** The length of a mult segment in a path, as a linear form *)
let length_mult { index ; mov ; suffix } =
  Index.( lenf mov *@ index + len suffix )

(** The length of a path, as a linear form *)
let length p =
  let rec aux : t -> Index.t = function
    | [] -> Index.const 0
    | l :: rest ->
      let l_prefix = len l in
      let r = aux_mult rest in
      Index.(l_prefix + r)
  and aux_mult = function
    | [] -> Index.const 0
    | None::rest -> aux_wild rest
    | Some m ::rest -> Index.(length_mult m + aux_wild rest)
  and aux_wild = function
    | [] -> Index.const 0
    | idx::[] -> idx
  in
  aux p

open Constraint

module Domain = struct



end


(** Computation of Q_(m,m'), the polyhedron of dependencies between two paths. *)
module Dependencies = struct

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

  let overlap_no_mult (prefix1,wild1) (prefix2,wild2) =
    match Field.conflict prefix1 prefix2 with
    | None -> ff
    | Some _ -> 
      Index.(
        len_layer wild1 + len prefix1 === len_layer wild2 + len prefix2
      )

  let rec overlap_one_mult (prefix1,{ index; mov; suffix },wild1) (prefix2,wild2) =
    match Field.conflict prefix1 prefix2 with
    | None -> ff
    | Some (`eq, _) ->
      Index.(
        (lenf mov *@ index) + len suffix + len_layer wild1 ===
        len_layer wild2
      )
    | Some (`right, m) ->
      Index.(
        len m + (lenf mov *@ index) + len suffix + len_layer wild1 ===
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

  let overlap_two_mult (prefix1, mult1, wild1) (mult2, wild2) =
    match prefix1, mult1, mult2 with
    | (List.[],
       { index = idx1; mov = mov1; suffix = suffix1 },
       { index = idx2; mov = mov2; suffix = suffix2 })
      when equal_field mov1 mov2 ->
      (idx1 === idx2) &&&
      Index.(len suffix1 + len_layer wild1 === len suffix2 + len_layer wild2)
    | _ ->
      (* Here, we give up and just use lengths instead *)
      let idx1 : path = prefix1 :: Some mult1 :: wild1 in
      let idx2 : path = [] :: Some mult2 :: wild2 in
      length idx1 === length idx2

  let overlap (p1:path) (p2:path) = match simplify p1, simplify p2 with
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
    | []::(Some mult1)::wild1, []::(Some mult2)::wild2 ->
      overlap_two_mult (Field.empty,mult1,wild1) (mult2, wild2)
    | l1::(Some mult1)::wild1, l2::(Some mult2)::wild2 ->
      match Field.conflict l1 l2 with
      | None -> ff
      | Some ((`eq|`left), m) ->
        overlap_two_mult (m,mult2,wild2) (mult1, wild1)
      | Some (`right, m) ->
        overlap_two_mult (m,mult1,wild1) (mult2, wild2)

  let make = overlap
end
