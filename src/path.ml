
let rec hcf a b = if b = 0 then a else hcf b (a mod b)

type t = [] | (::) of single * t
and single =
  | Word of word
  | Monome of monome
and monome = {
  index : Index.t ;
  word : word ;
}
and word = char list
and char = Any | Field of Field.field

type path = t

let rec vars : t -> _ = function
  | [] -> Id.Set.empty
  | Word _ :: t ->
    vars t
  | Monome { index ; _ } :: t ->
    Id.Set.union (Index.vars index) (vars t)

let rec map_vars f : t -> t = function
  | [] -> []
  | Word w :: t ->
    Word w :: map_vars f t
  | Monome { index ; word } :: t ->
    let index = Index.map_vars f index in
    Monome { index ; word } :: map_vars f t

let empty : t = []
let down ty pos : t = [Word [Field {ty; pos}]]
let many word index : t = [Monome { index ; word }]
let word : word -> t = function [] -> [] | word -> [Word word]
let wild index : t = [Monome { index ; word = [Any] }]
let of_fields : Field.t -> word
  = fun l -> List.map (fun x -> Field x) l
let word_of_fields l = word @@ of_fields l
let rec (++) e1 e2 = match e1 with
  | [] -> e2
  | h :: t -> h :: (t ++ e2)
        
module Word = struct

  type t = word

  let pp_char fmt = function
    | Field f -> Field.pp_field fmt f
    | Any -> Fmt.pf fmt ".φ"
  let pp fmt = Fmt.(list ~sep:nop pp_char) fmt
  
  let equal_char (c1 : char) (c2 : char) = match c1, c2 with
    | Any, Any -> true
    | Field f1, Field f2 ->
      CCInt.equal f1.pos f2.pos && Types.equal f1.ty f2.ty
    | Any, Field _ | Field _, Any -> false
  let equal (w1 : t) w2 = CCList.equal equal_char w1 w2
  
  let match_char (c1 : char) (c2 : char) = match c1, c2 with
    | Any, _ | _, Any -> true
    | Field f1, Field f2 ->
      CCInt.equal f1.pos f2.pos && Types.equal f1.ty f2.ty
  let match_ (w1 : t) w2 = CCList.equal match_char w1 w2

  let empty : t = []
  let length = List.length

  (** [conflict p1 p2] check if one path is prefix of the other.
      Return which one is shortest, along with the extra bits *)
  let rec conflict (p1 : word) (p2 : word) = match p1, p2 with
    | [], [] -> Some (`eq, empty)
    | [], l -> Some (`left, l)
    | l, [] -> Some (`right, l)
    | c1::t1, c2::t2 ->
      if match_char c1 c2 then conflict t1 t2 else None

  (** [count_prefix_and_split ~prefix w] returns [i,rest]
      such that [w = prefix^i ++ rest].
   **)
  let count_prefix_and_split ~prefix l =
    let len = List.length prefix in
    let rec take_prefix acc l =
      let start, rest = CCList.take_drop len l in
      if equal start prefix then
        take_prefix (acc + 1) rest
      else
        acc, l
    in
    take_prefix 0 l

  let count_suffix_and_split ~suffix l =
    let i, rest =
      count_prefix_and_split ~prefix:(List.rev suffix) (List.rev l)
    in
    i, List.rev rest
      

  (** [as_monome w] expresses [w] as a monome:
      Either w = r^i or w is not a power.
   **)
  let as_monome (w : word) =
    let len = List.length w in
    let rec try_increasing_prefix acc : word -> _ = function
      | [] -> None
      | h :: t ->
        let acc = List.cons h acc in
        let potential_root = List.rev acc in
        let potential_len = List.length potential_root in
        let k = len/potential_len in
        if equal w (CCList.repeat k potential_root) then
          Some (k, potential_root)
        else
          try_increasing_prefix acc t
    in
    try_increasing_prefix List.[] w

end
  
let pp_monome fmt { index; word } =
  match word with
  | [_] -> Fmt.pf fmt "%a^%a" Word.pp word Index.pp_parens index
  | _ -> Fmt.pf fmt "(%a)^%a" Word.pp word Index.pp_parens index

let simplify_monome m =
  match Word.as_monome m.word with
  | None -> m
  | Some (pow, word) ->
    let index = Index.mult pow m.index in
    { index ; word }

let rec simplify re = match re with
  | [] -> re
  | Word [] :: t ->
    simplify t
  | Word w :: t ->
    let t = simplify t in
    begin match t with
      | Word w' :: t -> 
        Word (w @ w') :: t
      | Monome { index; word } :: t ->
        let i, rest = Word.count_suffix_and_split ~suffix:word w in
        let index = Index.(index + const i) in
        begin match rest with
          | [] -> Monome { index ; word } :: t  
          | rest -> Word rest :: Monome { index ; word } :: t
        end
      | [] -> [Word w]
    end
  | Monome m :: t ->
    let { index ; word } = simplify_monome m in
    let t = simplify t in
    begin match t with
      | Word w :: t ->
        let i, rest = Word.count_prefix_and_split ~prefix:word w in
        let index = Index.(index + const i) in
        Monome { index ; word } :: Word rest :: t
      | Monome { index = index2 ; word = word2 } :: t
        when Word.equal word word2 ->
        let index = Index.(index + index2) in
        Monome { index ; word } :: t
      | _ ->
        Monome { index ; word } :: t
    end

let rec pp fmt (p: path) = match simplify p with
  | [] -> ()
  | Word w :: t -> Word.pp fmt w; pp fmt t
  | Monome f :: t -> pp_monome fmt f; pp fmt t
let pp_path = pp

(** The length of a path, as a linear form *)
let rec length : t -> Index.t = function
  | [] -> Index.const 0
  | Word w :: rest ->
    let l = Word.length w in
    Index.(const l + length rest)
  | Monome m :: rest ->
    let l = length_monome m in
    Index.(l + length rest)
and length_monome { index ; word } =
  Index.( Word.length word *@ index )

open Constraint

let height_var = Id.global "N"
    
(** Computation of D_m, the polyhedron of the domain of a paths. *)
module Domain = struct

  let make p =
    let l = length p in
    (Index.const 0 ==< l) &&&
    (l ==< Index.var height_var) &&&
    Id.Set.fold
      (fun k f -> (Index.const 0 ==< Index.var k) &&& f)
      (vars p)
      tt

end

(** Computation of Q_(m,m'), the polyhedron of dependencies between two paths. *)
module Dependencies = struct

  let index_nullable idx =
    if Index.is_nullable idx then
      idx === Index.const 0
    else
      ff

  let rec is_nullable : path -> _ = function
    | [] -> tt
    | Word [] :: t ->
      is_nullable t
    | Word _ :: _ ->
      ff
    | Monome { word = [] ; _ } :: t ->
      is_nullable t
    | Monome { index ; word = _ } :: t ->
      index_nullable index &&& is_nullable t
        
  let rec overlap (p1:path) (p2:path) = match simplify p1, simplify p2 with
    (* Both are empty *)
    | ([] | [Word []]), ([] | [Word []]) -> tt
    (* One of them is empty *)
    | l, ([] | [Word []])
    | ([] | [Word []]), l
      -> is_nullable l
    (* w1 == w2 ++ w'    rest1 == w' ++ rest2
       --------------------------------------
            w1 ++ rest1 == w2 ++ rest2
    *)
    | Word w1 :: rest1,
      Word w2 :: rest2 ->
      begin match Word.conflict w1 w2 with
        | Some (`eq,_) -> overlap rest1 rest2
        | Some (`right, w1) -> overlap (Word w1 :: rest1) rest2
        | Some (`left, w2) -> overlap rest1 (Word w2 :: rest2)
        | None -> ff
      end
    | Word w1 :: rest1, Monome { index ; word } :: rest2
    | Monome { index ; word } :: rest2, Word w1 :: rest1 ->
      begin match Word.conflict w1 word with
        (* w1, w don't conflict      f == 0     w1 ++ rest1 == rest2
           ---------------------------------------------------------
                w1 ++ rest1 == w^f ++ rest2
        *)
        | None ->
          index_nullable index &&&
          overlap (Word w1 :: rest1) rest2
        (* w1 = w      rest1 == w^(f-1) ++ rest2
           -------------------------------------
                w1 ++ rest1 == w^f ++ rest2
        *)
        | Some (`eq, _) ->
          let index = Index.decr index in
          overlap rest1 (Monome { index ; word } :: rest2)
        (* w1 = w ++ w'    w' ++ rest1 == w^(f-1) ++ rest2
           -----------------------------------------------
                     w1 ++ rest1 == w^f ++ rest2
        *)
        | Some (`right, w') ->
          let index = Index.decr index in
          overlap (Word w' :: rest1) (Monome { index ; word } :: rest2)
        (* w1 ++ w' = w    rest1 == (w' ++ w1)^(f-1) ++ w' ++ rest2
           -----------------------------------------------
                     w1 ++ rest1 == w^f ++ rest2
        *)
        | Some (`left, w') ->
          let index = Index.decr index in
          let word = w' @ w1 in
          overlap rest1 (Monome { index ; word } :: Word w' :: rest2)
      end

    (* Invariants:
       - Monomes are made of their simplest root.
       - The next monome doesn't have the same root.
       - The next word doesn't have a prefix that can be merged into the monome.
    *)
    (* f1 + n = f2    w^n ++ rest1 == rest2
       ------------------------------------
          w^f1 ++ rest1 == w^f2 ++ rest2
    *)
    | Monome { index = index1 ; word = word } :: rest1,
      Monome { index = index2 ; word = word' } :: rest2
      when Word.match_ word word' ->
      (* Thanks to the invariants, we know that the unfolding is *statically*
         finite, and that only one of the possibility is satisfiable *)
      let mk_cond1 i =
        Index.(index1 + i === index2) &&&
        overlap (Monome { index = i ; word } :: rest1) rest2
      and mk_cond2 i =
        Index.(index1 === index2 + i) &&&
        overlap rest1 (Monome { index = i ; word } :: rest2)
      in
      let n = Id.fresh "dummy" in
      let cond1 = mk_cond1 (Index.var n) and cond2 = mk_cond2 (Index.var n) in
      begin match Constraint.eval n cond1, Constraint.eval n cond2 with
        | None, None ->
          if present n cond1 && present n cond2 then
            assert false (* Cannot determine statically *)
          else 
            Index.(index1 === index2) &&& overlap rest1 rest2
        | Some n, None -> mk_cond1 (Index.const n)
        | None, Some n -> mk_cond2 (Index.const n)
        | Some 0, Some 0 ->
          Index.(index1 === index2) &&& overlap rest1 rest2
        | Some _, Some _ ->
          assert false (* Should never be satisfiable *)
      end

    (* ∧{k1=0..|w2|/m,k2=0..|w1|/m} 
       (f1=k1   f2=k2   w1^k1 ++ rest1 == w2^k2 ++ rest2)
       where m = HCF(|w1|,|w2|)
       --------------------------------------------------
               w1^f1 ++ rest1 == w2^f2 ++ rest2
    *)
    | Monome { index = index1 ; word = word1 } :: rest1,
      Monome { index = index2 ; word = word2 } :: rest2 ->
      let l1 = Word.length word1 and l2 = Word.length word2 in
      let max1 = l2 / hcf l1 l2 and max2 = l1 / hcf l1 l2 in
      let all_combinations =
        CCList.(product CCPair.make (range 0 max1) (range 0 max2))
        |> List.map (fun (k1, k2) ->
            let w1' = CCList.repeat k1 word1 and w2' = CCList.repeat k2 word2 in
            (index1 === Index.const k1) &&& (index2 === Index.const k2) &&&
            overlap (Word w1' :: rest1) (Word w2' :: rest2)
          )
      in
      (* Again, only one combination should be satisfiable. *)
      Constraint.or_ all_combinations

  let make p1 p2 =
    Constraint.(overlap p1 p2)
end
