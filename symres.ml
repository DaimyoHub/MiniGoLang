open Error
open Tast
open Ast

let fetch_struct_from_id (decls : tfile) (id : string) : structure t =
  match
    List.filter_map
      (function
       | TDstruct s -> if s.s_name = id then Some s else None
       | _ -> None)
      decls
  with
  | [s] -> return s
  | []  -> report Struct_not_found dummy_loc
  | _   -> report Several_structs dummy_loc

let fetch_func_from_id (decls : tfile) (id : string) : (function_ * expr) t =
  match
    List.filter_map
      (function
       | TDfunction (fn, body) ->
           if fn.fn_name = id then Some (fn, body) else None
       | _ -> None)
      decls
  with
  | [x] -> return x
  | [] -> report Func_not_found dummy_loc
  | _ -> report Several_funcs dummy_loc

let fetch_var_from_ctx (id : string) (ctx : (string * var) list) : var t =
  match List.assoc_opt id ctx with
  | Some v -> return v
  | None -> report Var_not_found dummy_loc
