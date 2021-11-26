
module ZZ = Z3overlay.Make (struct let ctx = Z3.mk_context [] end)
open ZZ

let rec index2smt h ({ monomes; constant } : Index.t) =
  let mk_monome (var, factor) =
    let sym = T.symbol @@
      Id.H.get_or_add h ~f:(fun n -> Symbol.declare Int @@ Id.to_string n) ~k:var
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

let check_conflict p1 p2 =
  let p1 = Path.map_vars Id.as_left p1 in
  let p2 = Path.map_vars Id.as_right p2 in
  let d1 = Path.Domain.make p1 in
  let d2 = Path.Domain.make p2 in
  let e = Path.Dependencies.make p1 p2 in
  let formula = constraint2smt (Id.H.create 17) Constraint.(e &&& d1 &&& d2) in
  (* Fmt.epr
   *   "@[<v2>Formula for conflict between@ %a@ %a"
   *   Path.pp p1 Path.pp p2
   * ; *)
  (* Fmt.epr
   *   ":@ %s@;<-2>Simplified:@ %s"
   *   (T.to_string formula)
   *   (T.to_string @@ T.simplify formula)
   * ; *)
  (* Fmt.epr "@]@."; *)
  begin match Solver.(check ~solver:(make ()) [formula]) with
    | Sat _model ->
      Some e
    | Unkown _ ->
      assert false
    | Unsat _ ->
      None
  end
