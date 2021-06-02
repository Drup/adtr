include Peahell.Make(struct

    let name = "adt4hpc"
    type input = Syntax.program
    let options = []
 
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
    let expect_parser = None 
    
    let exec fmt _import tyenv0 l =
      let f tyenv = function
        | Syntax.Declaration decl ->
          Types.Env.add decl.name decl tyenv
        | Rewrite r ->
          let r = Typing.type_rewrite tyenv r in
          Peahell.Report.printf "%a@." Rewrite.pp r;
          r.clauses |> List.iter (fun clause ->
              let depgraph = Rewrite.DepGraph.create clause in
              CCIO.File.with_temp ~prefix:"adt4hpc" ~suffix:".dot" (fun s ->
                  CCIO.with_out s @@ fun oc -> 
                  Rewrite.DepGraph.Dot.output_graph oc depgraph;
                  ignore @@ CCUnix.call "xdot %s" s;
                )
            );
          tyenv        
      in
      List.fold_left f tyenv0 l

  end)