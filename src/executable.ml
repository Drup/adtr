include Peahell.Make(struct

    let name = "adt4hpc"
    type input = Syntax.program

    let show_depgraph = ref false
    let options = [
      "--depgraph", Arg.Set show_depgraph, "Show the dependency graph. Requires xdot to be available."
    ]
 
    type environment = Types.Env.t
    let initial_environment = Types.Env.empty
                                
    let read_more str = 
      let i = ref (String.length str - 1) in
      while !i >= 0 && List.mem str.[!i] [' '; '\n'; '\t'; '\r'] do decr i done ;
      !i < 1 || (str.[!i] <> ';' || str.[!i - 1] <> ';')

    let file_parser =
      let f _name lexbuf =
        Peahell.Input.wrap (Parser.program Lexer.token) lexbuf
      in
      Some f
    let toplevel_parser = 
      let f lexbuf =
        Peahell.Input.wrap (Parser.toplevel_phrase Lexer.token) lexbuf
      in
      Some f
    let expect_parser = 
      let f _name lexbuf =
        Peahell.Input.wrap (Parser.expect_file Lexer.token) lexbuf        
      in
      Some ( "(*EXPECT", "*)", f)
    
    let exec fmt _import tyenv0 l =
      let f tyenv = function
        | Syntax.Declaration decl ->
          Types.Env.add decl.name decl tyenv
        | Rewrite r ->
          let cursor_moves = Typing.type_rewrite tyenv r in
          (* Peahell.Report.printf "%a@." (Rewrite.pp Field.pp) cursor_moves; *)
          let mem_moves = Rewrite.subtree2layer tyenv cursor_moves in
          Peahell.Report.printf "%a@." (Rewrite.pp Rewrite.Layer.pp) mem_moves;
          mem_moves.clauses |> List.iter (fun clause ->
              let g = Rewrite.WithLayer.create clause in
              if !show_depgraph then
                Rewrite.WithLayer.show g ;
              let sched = Scheduling.mk_schedule g in
              Fmt.pr "@[<2>Schedule: %a@]@."
                (Fmt.option ~none:(Fmt.any "None") Scheduling.pp_schedule) sched;
            );
          tyenv        
      in
      List.fold_left f tyenv0 l

  end)
