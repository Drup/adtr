(* The parser *)

%{

open Input.Parse
open Syntax
   
let make_loc (startpos, endpos) = Location.Location (startpos, endpos)

type error +=
   | Unclosed of Location.loc * string * Location.loc * string
              
let unclosed opening_name opening_loc closing_name closing_loc =
  raise(Error(Unclosed(make_loc opening_loc, opening_name,
                       make_loc closing_loc, closing_name)))

(* Error reporting *)
let prepare_error = function
  | Error (Unclosed (opening_loc, _opening, closing_loc, closing)) ->
     Some (Report.errorf
        ~loc:closing_loc
        ~sub:[opening_loc]
        "Syntax error: '%s' expected" closing)
  | _ -> None
let () = Report.register_report_of_exn prepare_error

  
%}

/* Tokens */
%token REWRITE
%token EOF
%token COMMA COLON DOT EQUAL
%token <string> LIDENT
%token <string> UIDENT
%token LPAREN RPAREN
%token LACCO RACCO
%token BAR ARROW
%token TYPE INT
%token <string> EXPECT


/* Entry points */

%type <Syntax.command> command
%start program
%type <Syntax.program> program
%start toplevel_phrase
%type <Syntax.program> toplevel_phrase
%start expect_file
%type <(Syntax.program * int * int) list> expect_file

%%

program: list(command) EOF {$1}
toplevel_phrase: list(command) DOT {$1}
expect_file: expect_item* EOF {$1}
%inline expect_item:
  | l = command+ EXPECT { l, $endofs(l), $endofs($2) }
;

command: type_declaration | rewrite { $1 };

type_declaration:
  TYPE
  name = tyconstr
  parameters=type_parameters
  EQUAL
  definition = definition
    { Declaration { name ; parameters; definition } }
;
type_parameters:
  | { [] }
  | LPAREN l = separated_list(COMMA,tyconstr) RPAREN { l }

definition:
  | BAR? l = separated_list(BAR,data_constructor) { Sum l }
;

data_constructor:
  | constructor=constr { {constructor; arguments = []} }
  | constructor=constr arguments=arguments { {constructor; arguments} }
arguments:
  | LPAREN l=separated_list(COMMA,type_expr) RPAREN { l }
;

(* Type expressions *)
simple_type_expr:
  | INT { TInt }
  | constructor = tyconstr { TConstructor { constructor; arguments = [] } }
  | LPAREN ty=type_expr RPAREN {ty}
;

type_expr:
  | ty=simple_type_expr {ty}
  | constructor = tyconstr arguments=arguments
    { TConstructor { arguments; constructor } }
;

rewrite:
  | f=var LPAREN parameters=parameters RPAREN COLON return_ty=type_expr
    EQUAL REWRITE discriminant=var LACCO clauses=clauses RACCO
    { Rewrite { f ; parameters ; return_ty ; discriminant ; clauses } }

parameters: l=separated_list(COMMA,parameter) { l }
parameter:
  | n=var COLON ty=simple_type_expr { n, ty }

clauses: BAR? l = separated_list(BAR,clause) { l }
clause:
  | p=pattern ARROW e=expr { (p,e) }

pattern:
  | constructor=constr
    { PConstructor {constructor; arguments = [] } }
  | constructor=constr
    LPAREN arguments=separated_list(COMMA,pattern) RPAREN
    { PConstructor {constructor; arguments } }
  | var=var { PVar var }

expr:
  | constructor=constr
    { EConstructor {constructor; arguments = [] } }
  | constructor=constr
    LPAREN arguments=separated_list(COMMA,expr) RPAREN
    { EConstructor {constructor; arguments } }
  | var=var { EVar var }

tyconstr: LIDENT {$1};
constr: UIDENT {$1};
var: LIDENT {$1};
