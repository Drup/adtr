
module LF = struct
    
  type t = int Index.index Index.index
  
  let import = Index.map_factors (fun i -> Index.const i)

  let ( * ) k x : t =
    Index.map_factors (fun f -> Index.(f * k)) x
  let ( *@ ) k x : t =
    Index.map_factors (fun f -> Index.(k *@ f)) x

  let (+) x1 x2 : t = Index.map2 (Index.plus) x1 x2
  let (-) x1 x2 : t = x1 + (-1 *@ x2)
  let sum l : t = List.fold_left (+) (import Index.zero) l

  let constvar x = Index.const @@ Index.var @@ x
  
  let wrap ~multipliers ~const lfs : t =
    constvar const
    + sum (List.map2 ( * ) multipliers lfs)

  let instanciate f lf =
    Index.map_factors (fun factor -> Index.eval f factor) lf


  let pp_monome fmt (var,k) = Fmt.pf fmt "%a*%a" Index.pp_parens k Id.pp var
  let pp fmt {Index. constant ; monomes } =
    match constant, monomes with
    | i, [] -> Index.pp_parens  fmt i
    | i, l ->
      Fmt.pf fmt "%a" Fmt.(hovbox @@ list ~sep:(any " +@ ") pp_monome) monomes;
      if constant = Index.zero then ()
      else Fmt.pf fmt " + %a" Index.pp_parens constant
end

let linearform_of_constraint c =
  let open Constraint in
  let rec aux = function
    | Constr (Eq (i1, i2)) ->
      let lf1 = Index.(i1 - i2) in
      let lf2 = Index.(i2 - i1) in
      [ lf1 ; lf2 ]
    | Constr (Leq (i1, i2)) ->
      let lf = Index.(i2 - i1) in
      [ lf ]
    | And l -> CCList.flat_map aux l
    | Or _ -> assert false
    | False -> raise Exit
    | True -> []
  in 
  try CCList.uniq ~eq:(=) @@ aux c with Exit -> []

let identify_factors (lf1 : LF.t) (lf2 : LF.t) =
  let constr0 = Constraint.(lf1.constant === lf2.constant) in
  let monomes1 = Index.map_of_monomes lf1.monomes in
  let monomes2 = Index.map_of_monomes lf2.monomes in
  let constrs =
    List.map snd @@ Id.Map.to_list @@ Id.Map.merge (fun _ f1 f2 ->
        match f1, f2 with
        | None, None -> None
        | None, Some f | Some f, None -> Some Constraint.(f === Index.zero)
        | Some f1, Some f2 -> Some Constraint.(f1 === f2)
      ) monomes1 monomes2
  in
  constr0 :: constrs


module G = Rewrite.WithLayer

let positivity_constraints g =
  G.fold_vertex (fun ({Rewrite. src ; dest ; name ; _ } as m) (lams, sigma) ->
      let src_slots = Rewrite.paths_of_src src in
      let dest_slots = Rewrite.paths_of_dest dest in
      let l = src_slots @ dest_slots in
      let constrs = Constraint.and_ (List.map Path.Domain.make l) in
      let system = linearform_of_constraint constrs in
      (* Fmt.epr "@[<v2>D_%a:@ %a@]@."
       *   Id.pp name
       *   (Fmt.list Index.pp) system
       *   ; *)
      let lamVec = List.map (fun _ -> Id.derive "??%s" name) system in
      let lam0 = Id.derive "??0%s" name in
      let lf = LF.wrap ~multipliers:lamVec ~const:lam0 system in
      (* Fmt.epr "@[<v2>??(%a) =@ %a@]@."
       *   Id.pp name
       *   LF.pp lf; *)
      (G.V.Map.add m (lamVec,lam0) lams, G.V.Map.add m lf sigma)
    )
    g (G.V.Map.empty, G.V.Map.empty)
  
let increasing_constraints sigmas g =
  G.fold_edges_e (fun edge (mus, epsilons, constrs) ->
      let src, q_edge, dest = edge in
      let system = linearform_of_constraint @@ Constraint.and_ q_edge in
      (* Fmt.epr "@[<v2>Q_(%a,%a):@ %a@]@."
       *   Id.pp src.name Id.pp dest.name
       *   (Fmt.list Index.pp) system
       *   ; *)
      let muVec = List.map (fun _ -> Id.fresh "??") system in
      let mu0 = Id.fresh "??0" in
      let lf1 = LF.wrap ~multipliers:muVec ~const:mu0 system in

      let epsilon = Id.fresh "??" in
      let sigma_src = Index.map_vars Id.as_left @@ G.V.Map.find src sigmas in
      let sigma_dest = Index.map_vars Id.as_right @@ G.V.Map.find dest sigmas in
      let lf2 = LF.(sigma_dest - sigma_src - constvar epsilon) in
      (* Fmt.epr "@[<v2>Eq_(%a,%a):@ %a@ =@ %a@]@."
       *   Id.pp src.name Id.pp dest.name
       *   LF.pp lf2 LF.pp lf1
       *   ; *)
      let new_constrs = identify_factors lf1 lf2 in

      (G.E.Map.add edge (muVec,mu0) mus,
       G.E.Map.add edge epsilon epsilons,
       new_constrs @ constrs
      )
    )
    g (G.E.Map.empty, G.E.Map.empty, [])

let all_vars f it =
  let open Constraint in 
  let f x = f (Index.var x) in  
  Iter.map (fun (l, constant) ->
      and_ (List.map f l) &&& f constant
    )
    it
  |> Iter.to_list

let sum_all_lambdas vars = 
  G.V.Map.values vars
  |> Iter.map (fun (lams, lam0) -> List.map Index.var (lam0 :: lams))
  |> Iter.to_list
  |> List.flatten
  |> Index.sum

let make_constraints g =
  let lambdas, sigmas = positivity_constraints g in
  let mus, epsilons, constraints = increasing_constraints sigmas g in
  (* Fmt.epr "@[<v2>Constraints after Farkas:@ %a@]@."
   *   (Fmt.list Constraint.pp) constraints; *)

  (* All 0 ??? ?? *)
  let lambdas_constraints =
    G.V.Map.values lambdas
    |> all_vars (fun c -> Constraint.(Index.zero ==< c))
  in
  (* All 0 ??? ?? *)
  let mus_constraints = 
    G.E.Map.values mus
    |> all_vars (fun c -> Constraint.(Index.zero ==< c))
  in
  let sum_all_vars =
    Iter.append (G.E.Map.values mus) (G.V.Map.values lambdas)
    |> Iter.map (fun (lams, lam0) -> List.map Index.var (lam0 :: lams))
    |> Iter.to_list
    |> List.flatten
    |> Index.sum
  in
  (* All 0 ??? ?? ??? 1 *)
  let epsilons_constraints =
    G.E.Map.values epsilons
    |> Iter.map Index.var
    |> Iter.map
      (fun c -> Constraint.((Index.zero ==< c) &&& (c ==< Index.const 1)))
    |> Iter.to_list
  in
  let all_constraints =
    lambdas_constraints @ mus_constraints @ epsilons_constraints @ constraints
  in
  Constraint.and_ all_constraints, `E epsilons, `Sum sum_all_vars, `S sigmas

let solve_with_smt constraints sum_epsilons sum_vars =
  let vars = Id.H.create 17 in
  let formula = Encode2SMT.constraint2smt vars constraints in
  let sum_epsilons = Encode2SMT.index2smt vars sum_epsilons in
  let sum_vars = Encode2SMT.index2smt vars sum_vars in
  (* Fmt.epr "@[<v2>Formula:@ %s@]@." Encode2SMT.ZZ.T.(to_string @@ simplify formula) ;
   * Fmt.epr "@[<v2>Optim:@ %s@]@." Encode2SMT.ZZ.T.(to_string @@ simplify optims) ; *)
  let res =
    let open Encode2SMT.ZZ.Optimize in
    let solver = make () in
    add ~solver formula;
    add ~solver Encode2SMT.ZZ.T.(sum_epsilons >= int 1);
    let _ = maximize ~solver sum_epsilons in
    let _ = minimize ~solver sum_vars in
    (* Fmt.epr "@[<v>Solver:@ %s@]@." (Z3.Optimize.to_string solver) ; *)
    check ~solver []
  in
  begin match res with
    | Sat (lazy model) ->
      (* Fmt.epr "@[<v2>Model:@ %s@." (Z3.Model.to_string model); *)
      let f v =
        Z.to_int @@
        Encode2SMT.ZZ.Model.get_value ~model @@
        Id.H.find vars v
      in
      Some f
    | Unkown _ ->
      None
    | Unsat _ ->
      None
  end 

let compute_schedule f sigmas =
  G.V.Map.map (LF.instanciate f) sigmas

let find_unconsumed_epsilons f epsilons =
  G.E.Map.filter (fun _ eps -> f eps = 0) epsilons

let sum_all_epsilons vars = 
  G.E.Map.values vars
  |> Iter.map Index.var
  |> Iter.to_list
  |> Index.sum

let mk_schedule1D ~formula ~sigmas ~epsilons ~sumvars =
  let sum_epsilons = sum_all_epsilons epsilons in
  match solve_with_smt formula sum_epsilons sumvars with
  | None ->
    (* Fmt.epr "No schedule@."; *)
    None
  | Some f ->
    let sched1D = compute_schedule f sigmas in
    let new_epsilons = find_unconsumed_epsilons f epsilons in
    Some (sched1D, new_epsilons)

let add_schedule sched1D sched =
  let merge1 _ x l = match x, l with
    | None, _ | _, None -> assert false
    | Some x, Some l -> Some (x::l)
  in
  G.V.Map.merge merge1 sched1D sched

let mk_schedule g =
  let formula, `E epsilons0, `Sum sumvars, `S sigmas = make_constraints g in
  let rec aux epsilons sched =
    if G.E.Map.is_empty epsilons then
      Some sched
    else
      match mk_schedule1D ~formula ~sigmas ~epsilons ~sumvars with
      | None -> None
      | Some (sched1D, epsilons') ->
        if G.E.Map.equal Id.equal epsilons epsilons' then failwith "PLOUF";
        aux epsilons' (add_schedule sched1D sched)
  in
  let empty_schedule = G.V.Map.map (fun _ -> []) sigmas in
  aux epsilons0 empty_schedule

let pp_schedule fmt sched =
  let f fmt (k, v) =
    Fmt.pf fmt "@[%a -> (%a)@]"
      Id.pp k.Rewrite.name
      (Fmt.list ~sep:Fmt.comma Index.pp) v
  in 
  Fmt.pf fmt "@[<v>%a@]" (Fmt.iter_bindings ~sep:Fmt.cut G.V.Map.iter f) sched
