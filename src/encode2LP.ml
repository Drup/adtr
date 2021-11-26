module Lp = struct
  include Lp
  let ivar (n : Name.t) : Lp.Poly.t = Lp.var ~integer:true ~lb:0. n
  let i v = Lp.c @@ float v
  let ( + ) = ( ++ )
  let sum = List.fold_left (+) Lp.zero
  let ( * ) = ( *~ )
end

module H = CCHashtbl.Make(Name)

let index2lp h ({ monomes; constant } : Index.t) =
  let mk_monome (var, factor) =
    let sym =
      H.get_or_add h ~f:Lp.ivar ~k:var
    in
    Lp.(i factor * sym)
  in
  Lp.sum (Lp.i constant :: List.map mk_monome monomes)


let ineq2lp h (ineq : int Constraint.ineq) = match ineq with
  | Constraint.Eq (e1, e2) ->
    Lp.(index2lp h e1 =~ index2lp h e2)
  | Constraint.Leq (e1, e2) ->
    Lp.(index2lp h e1 <~ index2lp h e2 + i 1)

let constraint2lp h (cnstr : int Constraint.ineq list) =
  List.map (ineq2lp h) cnstr

let check_conflict p1 p2 =
  let p2 = Path.refresh p2 in
  let n = Index.var "N" in
  let d1 = Constraint.as_conjunction @@ Path.Domain.make n p1 in
  let d2 = Constraint.as_conjunction @@ Path.Domain.make n p2 in  
  let check_validity conj =
    let h = H.create 17 in
    let cnstrs = constraint2lp h (d1 @ d2 @ conj) in
    (* We minimize the sum of all vars, since it's always bounded by 0 *)
    let optim = Lp.sum @@ H.values_list h in
    let prob = Lp.make (Lp.minimize optim) cnstrs in
    Fmt.epr "Problem:@.%s@." (Lp.to_string ~short:true prob);    
    match Lp_glpk.solve ~term_output:false prob with
    | Error _s ->
      Fmt.epr "  Error: %s@." _s;
      None
    | Ok (_, _) ->
      let f = Constraint.and_ @@ List.map (fun x -> Constraint.Constr x) conj in
      Some f
  in
  match Path.Dependencies.make p1 p2 with
  | True -> Some Constraint.tt
  | False -> None
  | e -> 
    Fmt.epr
      "@[Conflict between@ %a@ %a@]@."
      Path.pp p1 Path.pp p2
    ;
    Fmt.epr "  @[<v2>Domains:@ @[%a@]@ @[%a@]@]@."
      Constraint.pp (Constraint.from_wnf [d1])
      Constraint.pp (Constraint.from_wnf [d2]);
    Fmt.epr "  @[Formula:@ %a@]@."
      Constraint.pp e;
    let disj = Constraint.wnf e in
    Fmt.epr "  @[WNF:@ %a@]@."
      Constraint.pp (Constraint.from_wnf disj);
    let valid_conjs = CCList.filter_map check_validity disj in
    Fmt.epr "  @[Result:@ %a@]@."
      Constraint.pp (Constraint.or_ valid_conjs);
    match valid_conjs with
    | [] -> None
    | [x] -> Some x
    | _ -> assert false
