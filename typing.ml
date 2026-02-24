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

module Util = struct

  let rec typ_of_ptyp (decls : tfile) (pt : ptyp) : typ t =
    match pt with
    | PTident id ->
        (match id.id with
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
    (* Check if a parameter is called _ and report errror *)
    if List.find_opt (fun (ident, _) -> ident.id = "_") func.pf_params <> None then
      report Underscore_as_param func.pf_name.loc
    else
    let loc = func.pf_name.loc in
    let* param_typs =
      Util.map_typs decls (List.map snd func.pf_params) <?> (Params, loc)
    in
    let* ret_typs = Util.map_typs decls func.pf_typ <?> (Return, loc) in
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

    let ret_typ = typ_of_typ_list fn_sig.fn_typ in

    let mk e t = return { expr_desc = e; expr_typ = t } in

    let init_ctx = List.map (fun v -> (v.v_name, v)) fn_sig.fn_params in

    let rec gen_exprs ctx (es : pexpr list) : expr list Error.t =
      List.fold_right
        (fun e acc ->
          let* tes = acc <?> dummy_err in
          let* te  = gen_expr ctx e <?> dummy_err in
          return (te :: tes))
        es (return [])

    and gen_expr (ctx : (string * var) list) (e : pexpr) : expr t =
      match e.pexpr_desc with

      | PEskip -> mk TEskip (Tmany [])

      | PEnil -> mk TEnil Tnil

      | PEconstant (Cbool   _ as c) -> mk (TEconstant c) Tbool
      | PEconstant (Cint    _ as c) -> mk (TEconstant c) Tint
      | PEconstant (Cstring _ as c) -> mk (TEconstant c) Tstring

      | PEident ident ->
          let* v = fetch_var_from_ctx ident.id ctx <?> (Ident, ident.loc) in
          v.v_used <- true;
          mk (TEident v) v.v_typ

      | PEbinop (bop, e1, e2) -> gen_binop ctx bop e1 e2

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
          let* t_lvalues = gen_exprs ctx lhss <?> (Lvalues, e.pexpr_loc) in
          let* t_rvalues = gen_exprs ctx rhss <?> (Rvalues, e.pexpr_loc) in
          if
            List.length t_lvalues = List.length t_rvalues &&
              List.for_all2
                (fun lval rval -> lval.expr_typ = rval.expr_typ)
                t_lvalues t_rvalues
          then mk (TEassign (t_lvalues, t_rvalues)) (Tmany [])
          else report Assignments e.pexpr_loc

      | PEvars (idents, typ_opt, vals) ->
          let* t_vals = gen_exprs ctx vals <?> (Rvalues, e.pexpr_loc) in
          if List.length idents <> List.length t_vals
          then report Arity e.pexpr_loc
          else begin
            match typ_opt with
            | Some ptyp ->
                let* typ =
                  typ_of_ptyp decls ptyp <?> (Unknown_typ, e.pexpr_loc)
                in
                if List.for_all (fun t_val -> t_val.expr_typ = typ) t_vals then
                  let t_vars =
                    List.map
                      (fun ident -> new_var ident.id ident.loc typ)
                      idents
                  in
                  mk (TEvars t_vars) (Tmany [])
                else report Var e.pexpr_loc
            | None ->
                match (List.find_opt (fun v-> v.pexpr_desc = PEnil) vals) with
                | Some v -> report Untyped_Nil_init v.pexpr_loc
                | None ->
                let t_vars =
                  List.map2
                    (fun ident t_val ->
                      new_var ident.id ident.loc t_val.expr_typ)
                    idents t_vals
                in
                mk (TEvars t_vars) (Tmany [])
          end
          
      | PEif (cond, e1, e2) ->
          let* t_cond = gen_expr ctx cond <?> (Cond, cond.pexpr_loc) in
          if t_cond.expr_typ <> Tbool then report Cond cond.pexpr_loc
          else
            let* t_e1 = gen_expr ctx e1 <?> (If_branch, e1.pexpr_loc)   in
            let* t_e2 = gen_expr ctx e2 <?> (Else_branch, e2.pexpr_loc) in
            begin
              match find_return_typ t_e1, find_return_typ t_e2 with
              | None, None -> mk (TEif (t_cond, t_e1, t_e2)) (Tmany [])
              | Some t1, Some t2 when t1 = t2 ->
                  mk (TEif (t_cond, t_e1, t_e2)) t1
              | _ -> report If e.pexpr_loc
            end

      | PEreturn exprs ->
          let* t_exprs = gen_exprs ctx exprs <?> (Return, e.pexpr_loc) in
          if
            ret_typ =
              (typ_of_typ_list
                (List.map (fun t_expr -> t_expr.expr_typ) t_exprs))
          then mk (TEreturn t_exprs) ret_typ
          else report Return e.pexpr_loc

      | PEblock exprs ->
          (* I report a dummy error to not flood the full error report. Blocks
             are used in every statements and it doesn't help to know that some
             of it is ill typed. *)
          let* t_exprs = gen_exprs ctx exprs <?> dummy_err in
          let t_ret =
            match List.find_map find_return_typ t_exprs with
            | Some t -> t
            | None -> Tmany []
          in
          mk (TEblock t_exprs) t_ret

      | PEfor (cond, body) ->
          let* t_cond = gen_expr ctx cond <?> (Cond, cond.pexpr_loc) in
          if t_cond.expr_typ <> Tbool then report Cond cond.pexpr_loc
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
          if te.expr_typ = Tint then mk (TEincdec (te, op)) Tint
          else report Incdec e.pexpr_loc

    and gen_call ctx (ident : Ast.ident) (args : pexpr list) : expr t =
      let* (fn, _) = fetch_func_from_id decls ident.id <?> dummy_err in
      let* t_args  = gen_exprs ctx args <?> (Args, ident.loc) in

      if fn.fn_name = "fmt.Print" then (has_print := true; mk (TEprint t_args) (Tnil))
      else if fn.fn_name = "main" then report Calling_main ident.loc
      
      else if List.length t_args <> List.length fn.fn_params then
        report Arity ident.loc
      else
        let typs_ok =
          List.for_all2
            (fun te param -> te.expr_typ = param.v_typ || te.expr_typ = Tnil)
            t_args fn.fn_params
        in
        if not typs_ok then report Args ident.loc
        else mk (TEcall (fn, t_args)) (Util.typ_of_typ_list fn.fn_typ)

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
      
      let cmp_eq () =               
        if ty1 = ty2 then mk (TEbinop (bop, t1, t2)) Tbool
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
      let* te = gen_expr ctx e <?> (Unop, e.pexpr_loc) in
      
      match uop with
       | Uneg  ->
           if te.expr_typ = Tint  then mk (TEunop (Uneg,  te)) Tint
           else report Unop e.pexpr_loc
       | Unot  ->
           if te.expr_typ = Tbool then mk (TEunop (Unot,  te)) Tbool
           else report Unop e.pexpr_loc
       | Uamp  -> mk (TEunop (Uamp,  te)) (Tptr te.expr_typ)
       | Ustar ->
           match te.expr_typ with
           | Tptr t -> mk (TEunop (Ustar, te)) t
           | _      -> report Unop e.pexpr_loc
    in

    gen_expr init_ctx func.pf_body

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
      [TDfunction (fmt_print, { expr_desc = TEskip; expr_typ = Tmany [] })]
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
