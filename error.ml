open Ast
open Tast
open Lib

type err =
  | Dummy
  | Lhs
  | Rhs
  | Binop
  | Unop
  | Lvalues
  | Rvalues
  | Assignments
  | Arity
  | Mismatch
  | Var
  | Cond
  | Block
  | Params
  | Return
  | Ident
  | If_branch
  | Else_branch
  | If
  | For_branch
  | Incdec
  | Args
  | Dot
  | Object
  | New

  | Func_not_found
  | Struct_not_found
  | Several_funcs
  | Several_structs
  | Calling_main
  | Main_not_found
  | Var_not_found
  | Field_not_found
  | Unknown_typ
  | Import_not_used
  | Main_non_void
  | Duplicate_fields 
  | Duplicate_params
  | Untyped_Nil_init
  | Underscore_as_param
  | Invalid_typ

type rep =
  | Rep of err * location * rep
  | Nil

type 'a t = ('a, rep) result

let bind x on_fail loc mapper =
  match x with
  | Ok x -> mapper x
  | Error l -> Error (Rep (on_fail, loc, l))

let ( <?> ) x (on_fail, loc) = x, (on_fail, loc)
let ( let* ) (x, (on_fail, loc)) = bind x on_fail loc

let return v = Ok v
let report err loc = Error (Rep (err, loc, Nil))open Ast

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos
let dummy_err = Dummy, dummy_loc
