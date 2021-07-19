(* The lexer definition *)

{
open Parser

type Input.Lex.error +=
  | Unterminated_comment of Location.loc

(* To buffer string literals *)

let string_buffer = Buffer.create 256
let reset_string_buffer () = Buffer.reset string_buffer
let get_stored_string () = Buffer.contents string_buffer
let store_string s = Buffer.add_string string_buffer s
let store_lexeme lexbuf = store_string (Lexing.lexeme lexbuf)

(* To store the position of the beginning of a string and comment *)
let comment_start_loc = ref [];;

let wrap_comment_lexer comment lexbuf =
  let start_loc = Location.of_lex lexbuf  in
  comment_start_loc := [start_loc];
  reset_string_buffer ();
  let _end_loc = comment lexbuf in
  let s = get_stored_string () in
  reset_string_buffer ();
  s(* ,
    * { start_loc with Location.loc_end = end_loc.Location.loc_end } *)

let error lexbuf e = raise (Input.Lex.Error(e, Location.of_lex lexbuf))
let error_loc loc e = raise (Input.Lex.Error(e, loc))

(* Update the current location with file name and line number. *)

let update_loc lexbuf line chars =
  let pos = lexbuf.Lexing.lex_curr_p in
  let new_file = pos.pos_fname in
  lexbuf.lex_curr_p <- { pos with
    pos_fname = new_file;
    pos_lnum = pos.pos_lnum + line;
    pos_bol = pos.pos_cnum - chars;
  }

(* Error report *)

let prepare_error = function
  | Input.Lex.Error (Unterminated_comment _, loc) ->
    Some (Report.errorf ~loc "Comment not terminated")
  | _ -> None

let () =
  Report.register_report_of_exn prepare_error


(* The table of keywords *)

let keyword_table =
  CCHashtbl.of_list [
    "rewrite", REWRITE;
    "int", INT;
    "type", TYPE;
]

}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let digit = ['0'-'9']
let other = [ '\'']
let identchar = lowercase|uppercase|digit|other

rule token = parse
  | newline
      { update_loc lexbuf 1 0;
        token lexbuf }
  | blank +
      { token lexbuf }
  | lowercase identchar* as name
      { try Hashtbl.find keyword_table name
        with Not_found -> LIDENT name }
  | uppercase identchar* as name
      { try Hashtbl.find keyword_table name
        with Not_found -> UIDENT name }
  | "(*EXPECT"
      { let s = wrap_comment_lexer comment lexbuf in
        EXPECT s }
  | "(*"
      { let _ = wrap_comment_lexer comment lexbuf in
        token lexbuf }
  | "("  { LPAREN }
  | ")"  { RPAREN }
  | "{"  { LACCO }
  | "}"  { RACCO }
  | "="  { EQUAL }
  | "->"  { ARROW }
  | ":"  { COLON }
  | "|"  { BAR }
  | ","  { COMMA }
  | "."  { DOT }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MULT }
  | "/" { DIV }
  | eof { EOF }
  | (_ as illegal_char)
      { error lexbuf (Peahell.Input.Lex.Illegal_character illegal_char) }

and comment = parse
    "(*"
      { comment_start_loc := (Location.of_lex lexbuf) :: !comment_start_loc;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | "*)"
      { match !comment_start_loc with
        | [] -> assert false
        | [_] -> comment_start_loc := []; Location.of_lex lexbuf
        | _ :: l -> comment_start_loc := l;
                  store_lexeme lexbuf;
                  comment lexbuf
       }
  | eof
      { match !comment_start_loc with
        | [] -> assert false
        | loc :: _ ->
          let start = List.hd (List.rev !comment_start_loc) in
          comment_start_loc := [];
          error_loc loc (Unterminated_comment start)
      }
  | newline
      { update_loc lexbuf 1 0;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | _
      { store_lexeme lexbuf; comment lexbuf }
