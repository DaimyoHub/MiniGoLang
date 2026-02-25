(** Static type checking of Mini Go programs *)

open Lib
open Ast
open Tast
open Error
open Symres

let debug = ref false

let has_print = ref false
let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

let new_var : string -> Ast.location -> typ -> var =
  let id = ref 0 in
  fun x loc ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty;
      v_used = false; v_addr = false; v_ofs = -1 }

(* I have to overload type equality because of the fact that we can type some
   structure field in a structure A with a pointer to A. If we use usual
   structural equality in the typechecker, and try to analyze the following bloc
   of code :

   struct ABR {
     left : ABR*
     right : ABR*
     value : T
   }

   We fall in an infinite loop. *)
let ( == ) t1 t2 =
  let rec eq t1 t2 = match t1, t2 with
    | Tint,    Tint    -> true
    | Tbool,   Tbool   -> true
    | Tstring, Tstring -> true
    | Tnil,    Tnil    -> true
    | Tptr t1, Tptr t2 -> eq t1 t2
    | Tstruct s1, Tstruct s2 -> Stdlib.(==) s1 s2
    | Tmany ts1, Tmany ts2 ->
        List.length ts1 = List.length ts2 &&
        List.for_all2 eq ts1 ts2
    | _ -> false
  in
  eq t1 t2

module Desugar = struct
  open Ast

  (* Build PEident expression from an ident *)
  let pe_ident (id:ident) : pexpr =
    { pexpr_desc = PEident id; pexpr_loc = id.loc }

  (* Desugar inside a list of statements (block contents).
     This is where we can expand one stmt into multiple stmts. *)
  let rec ds_stmt_list (es : pexpr list) : pexpr list =
    List.concat_map ds_stmt es

  (* Desugar one "statement-ish" expression into 1 or more statements *)
  and ds_stmt (e : pexpr) : pexpr list =
    match e.pexpr_desc with
    | PEblock es ->
        let es' = ds_stmt_list es in
        [ { e with pexpr_desc = PEblock es' } ]

    | PEif (c, t, f) ->
        let c' = ds_expr c in
        let t' = ds_expr t in
        let f' = ds_expr f in
        [ { e with pexpr_desc = PEif (c', t', f') } ]

    | PEfor (c, body) ->
        let c' = ds_expr c in
        let body' = ds_expr body in
        [ { e with pexpr_desc = PEfor (c', body') } ]

    | PEassign (lhs, rhs) ->
        [ { e with pexpr_desc = PEassign (List.map ds_expr lhs, List.map ds_expr rhs) } ]

    | PEreturn rs ->
        [ { e with pexpr_desc = PEreturn (List.map ds_expr rs) } ]

    | PEincdec (x, op) ->
        [ { e with pexpr_desc = PEincdec (ds_expr x, op) } ]

    | PEvars (ids, Some t, vals) when vals <> [] ->
        (* IMPORTANT: only safe for typed vars. *)
        let decl =
          { e with pexpr_desc = PEvars (ids, Some t, []) }
        in
        let assign =
          { pexpr_desc = PEassign (List.map pe_ident ids, List.map ds_expr vals);
            pexpr_loc  = e.pexpr_loc; }
        in
        [ decl; assign ]

    | PEvars (ids, typ_opt, vals) ->
        (* Leave untyped-with-init alone; still recurse into RHS expressions. *)
        let vals' = List.map ds_expr vals in
        [ { e with pexpr_desc = PEvars (ids, typ_opt, vals') } ]

    | _ ->
        (* Expression-statement, etc. Just recurse in place. *)
        [ ds_expr e ]

  (* Desugar inside expressions: here we can’t expand into multiple statements,
     so we just rebuild recursively. *)
  and ds_expr (e : pexpr) : pexpr =
    let d = e.pexpr_desc in
    let d' =
      match d with
      | PEskip | PEnil | PEconstant _ | PEident _ -> d

      | PEunop (op, a) -> PEunop (op, ds_expr a)
      | PEbinop (op, a, b) -> PEbinop (op, ds_expr a, ds_expr b)

      | PEcall (f, args) -> PEcall (f, List.map ds_expr args)

      | PEdot (a, fld) -> PEdot (ds_expr a, fld)

      | PEassign (lhs, rhs) ->
          PEassign (List.map ds_expr lhs, List.map ds_expr rhs)

      | PEvars (ids, typ_opt, vals) ->
          (* NOTE: do not split here; splitting happens in ds_stmt within blocks. *)
          PEvars (ids, typ_opt, List.map ds_expr vals)

      | PEif (c, t, f) -> PEif (ds_expr c, ds_expr t, ds_expr f)

      | PEreturn rs -> PEreturn (List.map ds_expr rs)

      | PEblock es -> PEblock (ds_stmt_list es)

      | PEfor (c, body) -> PEfor (ds_expr c, ds_expr body)

      | PEincdec (x, op) -> PEincdec (ds_expr x, op)
    in
    { e with pexpr_desc = d' }

  (* Entry point for a function body *)
  let desugar_body (body : pexpr) : pexpr =
    ds_expr body
end

module Util = struct

  let rec typ_of_ptyp (decls : tfile) (pt : ptyp) : typ t =
    match pt with
    | PTident ident ->
        (match ident.id with
         | "int"    -> return Tint
         | "bool"   -> return Tbool
         | "string" -> return Tstring
         | name     -> 
             let* s = fetch_struct_from_id decls name <?> dummy_err in
             return (Tstruct s))
    | PTptr inner ->
        let* t = typ_of_ptyp decls inner <?> dummy_err in
        return (Tptr t)

  let typ_of_typ_list = function
    | []  -> Tmany []
    | [t] -> t
    | ts  -> Tmany ts

  let map_typs (decls : tfile) (pts : ptyp list) : typ list t =
    List.fold_right
      (fun pt acc ->
        let* ts = acc <?> dummy_err in
        let* t  = typ_of_ptyp decls pt <?> dummy_err in
        return (t :: ts))
      pts (return [])

  let rec find_return_typ (e : expr) : typ option =
    match e.expr_desc with
    | TEreturn _ -> Some e.expr_typ
    | TEblock es -> List.find_map find_return_typ es
    | TEif (_, e1, e2) ->
        (match find_return_typ e1 with
         | Some t -> Some t
         | None -> find_return_typ e2)
    | TEfor (_, body) -> find_return_typ body
    | _ -> None

  let rec typ_of_string (decls : tfile) str =
    match str with
    | "int"    -> return Tint
    | "bool"   -> return Tbool
    | "string" -> return Tstring
    | _ ->
        let n = String.length str in
        if n > 0 then
          if str.[0] = '*' then
            let* rec_typ =
              typ_of_string decls (String.sub str 1 (n - 1)) <?> dummy_err
            in return (Tptr rec_typ)
          else
            let* strc = fetch_struct_from_id decls str <?> dummy_err in
            return (Tstruct strc)
        else report Invalid_typ dummy_loc


  let is_nilable = function Tptr _ | Tnil -> true | _ -> false

end

module Func = struct

  (* TODO: Maybe use hashtable if there is nothing else to do in the project *)
  let rec find_dup_param (params : (Ast.ident * ptyp) list) :  Ast.ident option  =
    match params with
    | [] -> None
    | (ident, _) :: rest ->
        if List.exists (fun (id, _) -> id.id = ident.id) rest then Some ident
        else find_dup_param rest
  let gen_signature (decls : tfile) (func : pfunc) : function_ t =
    if List.exists (fun td ->
      match td with
      | TDfunction (f, _) when f.fn_name = func.pf_name.id -> true
      | _ -> false)
      decls
    then report Several_funcs func.pf_name.loc
    else
      match find_dup_param func.pf_params with
          | Some ident -> report Duplicate_params ident.loc
          | None -> (
    let open Util in
    
    let loc = func.pf_name.loc in
    let* param_typs =
      map_typs decls (List.map snd func.pf_params) <?> (Params, loc)
    in
    let* ret_typs = map_typs decls func.pf_typ <?> (Return, loc) in
    let params =
      List.map2
        (fun (ident, _) ty -> new_var ident.id ident.loc ty)
        func.pf_params param_typs
    in
    return
      { fn_name   = func.pf_name.id;
        fn_params = params;
        fn_typ    = ret_typs } )

  let gen_body (fn_sig : function_) (decls : tfile) (func : pfunc) : expr t =
    let open Util in
    let open Desugar in

    let ret_typ = typ_of_typ_list fn_sig.fn_typ in
    let compatible_param_arg (p:typ) (a:typ) = a == p || (a == Tnil && Util.is_nilable p) in 

    let get_multi_returns (te:expr) : typ list option =
      match te.expr_typ with
      | Tmany rets when List.length rets >= 2 -> Some rets
      | _ -> None in 

    let mk e t = return { expr_desc = e; expr_typ = t } in

    let init_ctx = List.map (fun v -> (v.v_name, v)) fn_sig.fn_params in

    let rec gen_exprs ctx (es : pexpr list) gen : expr list Error.t =
      List.fold_right
        (fun e acc ->
          let* tes = acc <?> dummy_err in
          let* te  = gen ctx e <?> dummy_err in
          return (te :: tes))
        es (return [])
    and lvalue (ctx : (string * var) list) (e : pexpr) : expr t = 
      match e.pexpr_desc with 
      | PEident p when p.id = "_" ->
        mk (TEident (new_var "_" p.loc (Tmany []))) (Tmany [])

      | PEident _ -> gen_expr ctx e
      | PEunop (Ustar, e') ->
        if e'.pexpr_desc = PEnil then report Nil_Deref e.pexpr_loc
        else
          let* te = gen_expr ctx e' <?> (Lvalues, e.pexpr_loc) in
          (match te.expr_typ with
           | Tptr t -> mk (TEunop (Ustar, te)) t
           | _ -> report Lvalues e.pexpr_loc)
      | PEdot (e', ident) ->
        let* te' = lvalue ctx e' <?> (Lvalues, e.pexpr_loc) in 
          gen_expr ctx e
      | _ -> report Lvalues e.pexpr_loc
    and gen_expr (ctx : (string * var) list) (e : pexpr) : expr t =
      match e.pexpr_desc with

      | PEskip -> mk TEskip (Tmany [])

      | PEnil -> mk TEnil Tnil

      | PEconstant (Cbool   _ as c) -> mk (TEconstant c) Tbool
      | PEconstant (Cint    _ as c) -> mk (TEconstant c) Tint
      | PEconstant (Cstring _ as c) -> mk (TEconstant c) Tstring
      | PEident ident when ident.id <> "_" ->
          let* v = fetch_var_from_ctx ident.id ctx <?> (Ident, ident.loc) in
          v.v_used <- true;
          mk (TEident v) v.v_typ
      | PEident ident when ident.id = "_" ->
          report Underscore ident.loc
      | PEident ident->
          let* v = fetch_var_from_ctx ident.id ctx <?> (Ident, ident.loc) in
          v.v_used <- true;
          mk (TEident v) v.v_typ

      | PEbinop (bop, e1, e2) -> gen_binop ctx bop e1 e2
      | PEunop (Ustar, _) -> lvalue ctx e
      | PEunop (uop, e) -> gen_unop ctx uop e

      | PEcall (ident, args) -> gen_call ctx ident args

      | PEdot (e, field_id) ->
          let* te = gen_expr ctx e <?> (Dot, e.pexpr_loc) in
          (match te.expr_typ with
           | Tstruct s ->
               (match Hashtbl.find_opt s.s_fields field_id.id with
                | Some f -> mk (TEdot (te, f)) f.f_typ
                | None -> report Field_not_found field_id.loc)
           | Tptr (Tstruct s) ->
               let deref =
                 { expr_desc = TEunop (Ustar, te);
                   expr_typ = Tstruct s }
               in
               (match Hashtbl.find_opt s.s_fields field_id.id with
                | Some f -> mk (TEdot (deref, f)) f.f_typ
                | None -> report Field_not_found field_id.loc)
           | _ -> report Dot e.pexpr_loc)

      | PEassign (lhss, rhss) ->
          let* t_lvalues = gen_exprs ctx lhss lvalue <?> (Lvalues, e.pexpr_loc) in
          let* t_rvalues = gen_exprs ctx rhss gen_expr <?> (Rvalues, e.pexpr_loc) in

          let lhs_tys = List.map (fun lv -> lv.expr_typ) t_lvalues in

          let ok =
            (* Case A: normal parallel assignment x1,..,xn = y1,..,yn *)
            if List.length t_lvalues = List.length t_rvalues then
              List.for_all2
                (fun lval rval -> compatible_param_arg lval.expr_typ rval.expr_typ)
                t_lvalues t_rvalues
            else
              (* Case B: expansion assignment x1,..,xn = g() where g() returns n values (n>=2) *)
              match t_rvalues with
              | [single] ->
                  (match get_multi_returns single with
                  | Some rets ->
                      List.length rets = List.length lhs_tys
                      && List.for_all2 compatible_param_arg lhs_tys rets
                  | None -> false)
              | _ -> false
          in

          if ok then mk (TEassign (t_lvalues, t_rvalues)) (Tmany [])
          else report Assignments e.pexpr_loc

      | PEvars (idents, typ_opt, vals) ->
          let* t_vals = gen_exprs ctx vals gen_expr <?> (Rvalues, e.pexpr_loc) in
          begin
            match typ_opt with
      | Some ptyp ->
          let* typ =
            typ_of_ptyp decls ptyp <?> (Unknown_typ, e.pexpr_loc)
          in

          let n = List.length idents in

          let ok =
            match t_vals with
            | [] ->
                true

            (* normal init: var x,y T = e1,e2 *)
            | _ when List.length t_vals = n ->
                List.for_all (fun tv -> compatible_param_arg typ tv.expr_typ) t_vals

            (* multi-return init: var x,y T = g() where g returns (T,T) *)
            | [single] ->
                (match get_multi_returns single with
                | Some rets ->
                    List.length rets = n
                    && List.for_all (fun rt -> compatible_param_arg typ rt) rets
                | None -> false)

            | _ -> false
          in

          if not ok then report Var e.pexpr_loc
          else
            let t_vars =
              List.map (fun ident -> new_var ident.id ident.loc typ) idents
            in
            mk (TEvars (List.filter (fun v -> v.v_name <> "_") t_vars)) (Tmany [])

      | None ->
          let n = List.length idents in

          let is_untyped_nil (te:expr) = (te.expr_typ == Tnil) in

          (* Case A: normal inference var x1..xn = e1..en *)
          let ok_normal =
            List.length t_vals = n
            && List.for_all (fun tv -> not (is_untyped_nil tv)) t_vals
          in

          (* Case B: multi-return inference var x1..xn = g() *)
          let ok_expand, inferred_tys =
            match t_vals with
            | [single] ->
                (match get_multi_returns single with
                | Some rets when List.length rets = n ->
                    (* forbid untyped nil in inferred types *)
                    if List.exists (fun t -> t == Tnil) rets then (false, [])
                    else (true, rets)
                | _ -> (false, []))
            | _ -> (false, [])
          in

          if ok_normal then
            let t_vars =
              List.map2
                (fun ident t_val -> new_var ident.id ident.loc t_val.expr_typ)
                idents t_vals
            in
            mk (TEvars t_vars) (Tmany [])
          else if ok_expand then
            let t_vars =
              List.map2
                (fun ident ty -> new_var ident.id ident.loc ty)
                idents inferred_tys
            in
            mk (TEvars t_vars) (Tmany [])
          else
            if List.length t_vals <> n then report Arity e.pexpr_loc
            else
              match List.find_opt (fun v -> v.pexpr_desc = PEnil) vals with
              | Some v -> report Untyped_Nil_init v.pexpr_loc
              | None -> report Arity e.pexpr_loc
                end
                
            | PEif (cond, e1, e2) ->
                let* t_cond = gen_expr ctx cond <?> (Cond, cond.pexpr_loc) in               
                if not (t_cond.expr_typ == Tbool) then report Cond cond.pexpr_loc
                else
                  let* t_e1 = gen_expr ctx e1 <?> (If_branch, e1.pexpr_loc)   in
                  let* t_e2 = gen_expr ctx e2 <?> (Else_branch, e2.pexpr_loc) in
                  begin
                    match find_return_typ t_e1, find_return_typ t_e2 with
                    | None, None -> mk (TEif (t_cond, t_e1, t_e2)) (Tmany [])
                    | Some t1, Some t2 when t1 == t2 ->
                        mk (TEif (t_cond, t_e1, t_e2)) t1
                    (* If the conditional returns in the first branch and does not
                      define the else branch, we shouldn't check branches typing
                      constraints (because there are none). *)
                    | Some t, None when t_e2.expr_desc = TEskip ->
                        mk (TEif (t_cond, t_e1, t_e2)) t
                    | _ -> report If e.pexpr_loc
            end

      | PEreturn exprs ->
          let* t_exprs = gen_exprs ctx exprs gen_expr <?> (Return, e.pexpr_loc) in
          if
            ret_typ ==
              (typ_of_typ_list
                (List.map (fun t_expr -> t_expr.expr_typ) t_exprs))
          then mk (TEreturn t_exprs) ret_typ
          else report Return e.pexpr_loc

      | PEblock exprs ->
          (* I report a dummy error to not flood the full error report. Blocks
             are used in every statements and it doesn't help to know that some
             of it is ill typed. *)
          let rec gen_block ctx acc = function
            | [] ->
                let t_exprs = List.rev acc in
                let t_ret =
                  match List.find_map find_return_typ t_exprs with
                  | Some t -> t
                  | None -> Tmany []
                in
                mk (TEblock t_exprs) t_ret
            | e :: rest ->
                let* te = gen_expr ctx e <?> dummy_err in
                (* We mustn't forget that each time with declare a variable it
                   should be added to the current's block context. *)
                let ctx' =
                  match te.expr_desc with
                  | TEvars vars ->
                      List.fold_left (fun ctx v -> (v.v_name, v) :: ctx) ctx vars
                  | _ -> ctx
                in
                gen_block ctx' (te :: acc) rest
          in
          gen_block ctx [] exprs

      | PEfor (cond, body) ->
          let* t_cond = gen_expr ctx cond <?> (Cond, cond.pexpr_loc) in
          if not (t_cond.expr_typ == Tbool) then report Cond cond.pexpr_loc
          else
            let* t_body = gen_expr ctx body <?> (For_branch, body.pexpr_loc) in
            let t_ret = 
              match find_return_typ t_body with
              | None -> Tmany []
              | Some typ -> typ
            in
            mk (TEfor (t_cond, t_body)) t_ret

      | PEincdec (e, op) ->
          let* te = gen_expr ctx e <?> (Incdec, e.pexpr_loc) in
          if te.expr_typ == Tint then mk (TEincdec (te, op)) Tint
          else report Incdec e.pexpr_loc

  and gen_call (ctx : (string * var) list) (ident : Ast.ident) (args : pexpr list) : expr t =
    (* The parser generates a classic call expression when finding the new
      keyword. So we should handle typechking of it differently from other
      calls before the function's name resolution. *)
    if ident.id = "new" then
      match List.map (fun p -> p.pexpr_desc) args with
      | [PEident pident] ->
          let* typ = typ_of_string decls pident.id <?> (New, ident.loc) in
          mk (TEnew typ) (Tptr typ)
      | _ -> report New ident.loc
    else

    let* (fn, _) = fetch_func_from_id decls ident.id <?> dummy_err in
    let* t_args  = gen_exprs ctx args gen_expr <?> (Args, ident.loc) in

    (* Builtins / special cases *)
    if fn.fn_name = "fmt.Print" then
      (has_print := true; mk (TEprint t_args) (Tmany []))
    else if fn.fn_name = "main" then
      report Calling_main ident.loc
    else
      let param_tys = List.map (fun p -> p.v_typ) fn.fn_params in

      let compatible_param_arg (p:typ) (a:typ) =
        a == p || (a == Tnil && Util.is_nilable p)
      in

      let tys_compatible (ps:typ list) (as_:typ list) =
        List.length ps = List.length as_ &&
        List.for_all2 compatible_param_arg ps as_
      in

      (* Case 1: normal call f(e1,...,en) *)
      let ok_normal =
        tys_compatible param_tys (List.map (fun a -> a.expr_typ) t_args)
      in

      (* Case 2: expansion call f(g()) where g() returns exactly n values *)
     let ok_expand =
      (match t_args with
      | [single] ->
          (match single.expr_typ with
          | Tmany rets ->
              (* IMPORTANT: only allow expansion for >= 2 returned values *)
              List.length rets >= 2 && tys_compatible param_tys rets
          | _ -> false)
      | _ -> false)
      in

      if not (ok_normal || ok_expand) then
        (* You can choose Arity vs Args, but Args is usually enough *)
        report Args ident.loc
      else
        mk (TEcall (fn, t_args)) (Util.typ_of_typ_list fn.fn_typ)

    and gen_binop ctx bop e1 e2 : expr t =
      let* t1 = gen_expr ctx e1 <?> (Lhs, e1.pexpr_loc) in
      let* t2 = gen_expr ctx e2 <?> (Rhs, e2.pexpr_loc) in
      
      let ty1 = t1.expr_typ and ty2 = t2.expr_typ in
      
      let ari () =
        match ty1, ty2 with
        | Tint, Tint -> mk (TEbinop (bop, t1, t2)) Tint
        | Tint, _ -> report Binop e2.pexpr_loc
        | _ -> report Binop e1.pexpr_loc
      in

      (* Same as in Vars/Assign, we shouldn't forget that we can find
         expressions such as 'ptr == nil'. *)
      let cmp_eq () =               
        if ty1 == ty2
          || (ty1 == Tnil && is_nilable ty2)
          || (ty2 == Tnil && is_nilable ty1)
        then mk (TEbinop (bop, t1, t2)) Tbool
        else report Binop e2.pexpr_loc
      in
      
      let cmp_ord () =
        match ty1, ty2 with
        | Tint, Tint -> mk (TEbinop (bop, t1, t2)) Tbool
        | Tint, _ -> report Binop e2.pexpr_loc
        | _ -> report Binop e1.pexpr_loc          
      in
      
      let log () =
        match ty1, ty2 with
        | Tbool, Tbool -> mk (TEbinop (bop, t1, t2)) Tbool
        | Tbool, _ -> report Binop e2.pexpr_loc
        | _ -> report Binop e1.pexpr_loc
      in

      match bop with
      | Bsub | Bmul | Bdiv | Bmod -> ari ()
      | Beq  | Bne                -> cmp_eq ()
      | Blt  | Ble | Bgt | Bge    -> cmp_ord ()
      | Band | Bor                -> log ()
      | Badd ->
          match ty1, ty2 with
          | Tint, Tint -> mk (TEbinop (bop, t1, t2)) Tint
          | Tstring, Tstring -> mk (TEbinop (bop, t1, t2)) Tstring
          | Tint, _ | Tstring, _ -> report Binop e2.pexpr_loc
          | _ -> report Binop e1.pexpr_loc

    and gen_unop ctx uop e : expr t =
      
      match uop with
       | Uneg  ->
          let* te = gen_expr ctx e <?> (Unop, e.pexpr_loc) in
           if te.expr_typ == Tint  then mk (TEunop (Uneg,  te)) Tint
           else report Unop e.pexpr_loc
       | Unot  ->
          let* te = gen_expr ctx e <?> (Unop, e.pexpr_loc) in
           if te.expr_typ == Tbool then mk (TEunop (Unot,  te)) Tbool
           else report Unop e.pexpr_loc
       | Uamp  -> 
          let* te = lvalue ctx e <?> (Lvalues, e.pexpr_loc) in
          mk (TEunop (Uamp, te)) (Tptr te.expr_typ)
       | Ustar -> report Unop e.pexpr_loc
    in
    let body = Desugar.desugar_body func.pf_body in
    gen_expr init_ctx body

end

exception Err of Ast.location * Error.rep

let file ~debug:b (imp, dl : Ast.pfile) : Tast.tfile =
  debug := b;

  let tfile = ref [] in
  (* We first generate structures' typed declarations *)
  List.iter
    (function
     | PDstruct ps ->
         let strc : structure =
           { s_name   = ps.ps_name.id;
             s_fields = Hashtbl.create 4;
             s_list   = [];
             s_size   = 0 }
         in (if List.exists (fun td ->
           match td with
           | TDstruct s when s.s_name = ps.ps_name.id -> true
           | _ -> false)
           !tfile
         then raise (Err (ps.ps_name.loc, Rep (Several_structs, ps.ps_name.loc, Nil)))
         else ()
         );
         tfile := !tfile @ [TDstruct strc];
         let ofs = ref 0 in
         let fields =
           List.map (fun (fid, ftyp) ->
             match Util.typ_of_ptyp !tfile ftyp with
             | Error rep -> raise (Err (fid.loc, rep))
             | Ok ft ->
                 let f = { f_name = fid.id; f_typ = ft; f_ofs = !ofs } in
                 ofs := !ofs + 8;
                 if (Hashtbl.mem strc.s_fields fid.id) then raise (Err (fid.loc, Rep (Duplicate_fields, fid.loc, Nil)))
                 else Hashtbl.add strc.s_fields fid.id f;
                 f)
           ps.ps_fields
         in
         strc.s_list <- fields;
         strc.s_size <- !ofs
     | PDfunction _ -> ())
    dl;

  (* Then we generate functions' associated typed ASTs and signatures *)
  if imp then begin
    let fmt_print =
      { fn_name   = "fmt.Print";
        fn_params = [];
        fn_typ    = []; }
    in
    tfile :=
      (TDfunction (fmt_print, { expr_desc = TEskip; expr_typ = Tmany [] }))
        :: !tfile
  end;
  
  let main_defined = ref false in
  List.iter
    (function
     | PDstruct _ -> ()
     | PDfunction pf ->
           match Func.gen_signature !tfile pf with
           | Error rep -> raise (Err (pf.pf_name.loc, rep))
           | Ok fn_sig -> if pf.pf_name.id = "main" 
               then (main_defined := true; if fn_sig.fn_typ <> [] || fn_sig.fn_params <> [] then raise (Err (pf.pf_name.loc, Rep (Main_non_void, pf.pf_name.loc, Nil))));
               match Func.gen_body fn_sig !tfile pf with
               | Error rep -> raise (Err (pf.pf_name.loc, rep))
               | Ok body -> tfile := TDfunction (fn_sig, body) :: !tfile)
    dl;

  if not !main_defined then
    raise (Err (dummy_loc, Rep (Main_not_found, dummy_loc, Nil)))
  else if imp && not !has_print then
    raise (Err (dummy_loc, Rep (Import_not_used, dummy_loc, Nil)))
  else !tfile  
