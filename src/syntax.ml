type name = string

type 'a constr_app = {
  constructor : name ;
  arguments : 'a list ;
}

(** Types **)

type data_constructor = type_expr constr_app

and type_expr =
  | TInt
  | TVar of name
  | TConstructor of type_expr constr_app

and definition =
  | Sum of data_constructor list

and type_declaration = {
  name : name;
  parameters : name list; 
  definition : definition;
}

(** Rewrite rules *)

type pattern =
  | PConstructor of pattern constr_app
  | PVar of name

type expr = 
  | EConstructor of expr constr_app
  | EVar of name

type rewrite = {
  f : name ;
  parameters : (name * type_expr) list;
  return_ty : type_expr;
  discriminant: name;
  clauses : (pattern * expr) list;
}

and command =
  | Declaration of type_declaration
  | Rewrite of rewrite

and program = command list