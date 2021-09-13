
module ZZ = Z3overlay.Make (struct let ctx = Z3.mk_context [] end)
open ZZ

module H = CCHashtbl.Make(Name)
  
let rec index2smt h ({ monomes; constant } : Index.t) =
  let mk_monome (var, factor) =
    let sym = T.symbol @@
      H.get_or_add h ~f:(fun n -> Symbol.declare Int n) ~k:var
    in 
    T.(int factor * sym)
  in
  T.add (T.int constant :: List.map mk_monome monomes)

let rec constraint2smt h : _ Constraint.t -> _ = function
  | Constr (Eq (e1, e2)) ->
    T.(index2smt h e1 = index2smt h e2)
  | Constr (Leq (e1, e2)) ->
    T.(index2smt h e1 <= index2smt h e2)
  | And v -> T.and_ @@ List.map (constraint2smt h) v
  | Or v -> T.or_ @@ List.map (constraint2smt h) v
  | True -> T.true_
  | False -> T.false_

let sort = String
let decl_word base = Symbol.declare sort (Name.fresh base)

let concat_re = function
  | [] -> Z3Regex.from_seq (Z3Seq.empty sort)
  | [x] -> x
  | l -> Z3Regex.concat l

let as_re = Z3Regex.from_seq

let count_type =
  let h = Hashtbl.create 17 in
  let r = ref 0 in
  fun ty -> begin
      match Hashtbl.find_opt h ty with
      | Some i -> i
      | None ->
        let i = !r in
        incr r;
        Hashtbl.add h ty i;
        i
    end
      
let field2smt (l : Field.t) = 
  let aux {Field. ty; pos } =
    let i_ty = count_type ty in
    let i = Int.shift_left i_ty 4 lor pos in
    let c = Char.code ' ' + i in (* Make a printable char, helps Z3 ... *)
    Char.unsafe_chr c
  in
  let s = Z3Seq.of_string @@ CCString.of_list @@ List.map aux l in
  let len = List.length l in
  s, len

let path2smt s0 p =
  let vars = H.create 17 in
  let rec path : Path.t -> _ = function
    | [] -> [],[],Index.zero,[]
    | l :: rest ->
      let s, len = field2smt l in
      let rest_re, rest_s, rest_len, formula = mult rest in
      as_re s :: rest_re,
      s :: rest_s,
      Index.(const len + rest_len),
      formula
  and mult : Path.mult -> _ = function
    | [] -> [],[],Index.zero,[]
    | None :: rest -> layers rest
    | Some { index; mov; suffix } :: rest ->
      let s = T.symbol @@ decl_word "m" in
      let s_mov, len_mov = field2smt mov in
      let new_re = Z3Regex.(star @@ as_re s_mov) in
      let new_monome = Index.(len_mov *@ index) in
      let suffix_s, suffix_len = field2smt suffix in
      let rest_re, rest_s, rest_len, formula = layers rest in
      let i = index2smt vars new_monome in
      let f = T.(Z3Seq.length s = i) in
      new_re :: as_re suffix_s :: rest_re,
      s :: suffix_s :: rest_s,
      Index.(new_monome + Index.const suffix_len + rest_len),
      f :: formula
  and layers : Path.layers -> _ = function
    | [] -> [],[],Index.zero,[]
    | idx :: [] ->
      let i = index2smt vars idx in
      let s = T.symbol @@ decl_word "φ" in
      let f = T.(Z3Seq.length s = i) in
      [Z3Regex.any @@ Regex sort], [s], idx, [f]
  in
  let re, s, poly, formula = path p in
  let all_pos =
    List.map (fun x -> T.(!x >= int 0)) @@ H.values_list vars 
  in
  concat_re re,
  T.((Z3Seq.concat s = s0) &&
     (index2smt vars poly = Z3Seq.length s0) &&
     and_ formula &&
     and_ all_pos)

let check_conflict p1 p2 =
  let p2 = Path.refresh p2 in
  let s = T.symbol @@ decl_word "s" in
  let re1, formula1 = path2smt s p1 in
  let re2, formula2 = path2smt s p2 in
  let formula =
    T.(formula1 && formula2 &&
       Z3Regex.(in_re s (inter [re1;re2]))
      )
  in
  (* Fmt.epr
   *   "@[<v2>Formula for conflict between@ %a@ %a"
   *   Path.pp p1 Path.pp p2
   * ;
   * Fmt.epr
   *   ":@ %s@;<-2>Simplified:@ %s"
   *   (T.to_string formula)
   *   (T.to_string @@ T.simplify formula)
   * ;
   * Fmt.epr "@]@."; *)
  begin match Solver.(check ~solver:(make ()) [formula]) with
    | Sat _model ->
      let e = Path.Dependencies.make p1 p2 in
      Some e
    | Unkown _ ->
      Some Constraint.False
    | Unsat _ ->
      None
  end 
