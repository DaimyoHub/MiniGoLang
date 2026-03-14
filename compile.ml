open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in
  fun () -> incr r; "L_" ^ string_of_int !r

let stringToLabel : (string, string) Hashtbl.t = Hashtbl.create 5
let frame_sizes : (string, int) Hashtbl.t = Hashtbl.create 17


let is_atom_like = function
  | Tint | Tbool | Tnil | Tptr _ -> true
  | _ -> false
let emit_space =
  movq (ilab "SPACE_STR") (reg rdi) ++
  xorq (reg rax) (reg rax) ++
  call "printf"

let rec emit_print_one (p : expr) =
  expr p ++
  xorq (reg rax) (reg rax) ++
  match p.expr_typ with
  | Tstring ->
      movq (reg r10) (reg rdi) ++
      call "printf"
  | Tint ->
      movq (reg r10) (reg rsi) ++
      movq (ilab "INT_PRINTER") (reg rdi) ++
      call "printf"
  | Tbool ->
      call "print_bool_r10"
  | Tnil ->
      movq (ilab "NIL_STR") (reg rdi) ++
      xorq (reg rax) (reg rax) ++      
      call "printf"
  | Tptr _ ->
      let l_nil = new_label () in
      let l_end = new_label () in
      expr p ++
      cmpq (imm 0) (reg r10) ++
      je l_nil ++
      movq (reg r10) (reg rsi) ++
      movq (ilab "PTR_PRINTER") (reg rdi) ++
      xorq (reg rax) (reg rax) ++
      call "printf" ++
      jmp l_end ++
      label l_nil ++
      movq (ilab "NIL_STR") (reg rdi) ++
      xorq (reg rax) (reg rax) ++
      call "printf" ++
      label l_end
  | _ ->
      failwith "Unsupported type in print"

(* addr e:
   compute the address of an lvalue into r10 *)
and addr (e : expr) =
  match e.expr_desc with
| TEident v ->
    if v.v_addr then
      movq (ind ~ofs:v.v_ofs rbp) (reg r10)
    else
      leaq (ind ~ofs:v.v_ofs rbp) r10

  | TEdot (e1, f) ->
      addr e1 ++
      addq (imm f.f_ofs) (reg r10)

  | TEunop (Ustar, e1) ->
      expr e1

  | _ ->
      failwith "addr: not an lvalue"

(* expr e:
   compute the value of e into r10 *)
and expr (e : expr) =
  match e.expr_desc with
  | TEskip ->
      nop

  | TEconstant (Cstring s) ->
      let lab =
        match Hashtbl.find_opt stringToLabel s with
        | Some l -> l
        | None ->
            let l = new_label () in
            Hashtbl.add stringToLabel s l;
            l
      in
      movq (ilab lab) (reg r10)

  | TEconstant (Cint n) ->
      movq (imm64 n) (reg r10)

  | TEconstant (Cbool true) ->
      movq (imm 1) (reg r10)

  | TEconstant (Cbool false) ->
      xorq (reg r10) (reg r10)

  | TEnil ->
      xorq (reg r10) (reg r10)

  | TEident _ ->
      addr e ++
      movq (ind r10) (reg r10)

  | TEdot _ ->
      addr e ++
      movq (ind r10) (reg r10)

  | TEunop (Uamp, e1) ->
      addr e1

  | TEunop (Ustar, e1) ->
      expr e1 ++
      movq (ind r10) (reg r10)

  | TEunop (Uneg, e1) ->
      expr e1 ++
      negq (reg r10)

  | TEunop (Unot, e1) ->
      expr e1 ++
      cmpq (imm 0) (reg r10) ++
      sete (reg al) ++
      movzbq (reg al) r10

  | TEbinop (op, e1, e2) ->
      begin match op with
      | Badd ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          addq (reg r11) (reg r10)

      | Bsub ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          subq (reg r10) (reg r11) ++
          movq (reg r11) (reg r10)

      | Bmul ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          imulq (reg r11) (reg r10)

      | Bdiv ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++
          movq (reg r10) (reg r11) ++
          popq r10 ++
          movq (reg r10) (reg rax) ++
          cqto ++
          idivq (reg r11) ++
          movq (reg rax) (reg r10)

      | Bmod ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++
          movq (reg r10) (reg r11) ++
          popq r10 ++
          movq (reg r10) (reg rax) ++
          cqto ++
          idivq (reg r11) ++
          movq (reg rdx) (reg r10)

      | Band ->
          let l_false = new_label () in
          let l_end = new_label () in
          expr e1 ++
          cmpq (imm 0) (reg r10) ++
          je l_false ++
          expr e2 ++
          cmpq (imm 0) (reg r10) ++
          je l_false ++
          movq (imm 1) (reg r10) ++
          jmp l_end ++
          label l_false ++
          movq (imm 0) (reg r10) ++
          label l_end

      | Bor ->
          let l_true = new_label () in
          let l_end = new_label () in
          expr e1 ++
          cmpq (imm 0) (reg r10) ++
          jne l_true ++
          expr e2 ++
          cmpq (imm 0) (reg r10) ++
          jne l_true ++
          movq (imm 0) (reg r10) ++
          jmp l_end ++
          label l_true ++
          movq (imm 1) (reg r10) ++
          label l_end

      | Beq when e1.expr_typ = Tstring ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          call "string_eq_r11_r10"

      | Bne when e1.expr_typ = Tstring ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          call "string_eq_r11_r10" ++
          xorb (imm 1) (reg r10b)

      | Beq ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          sete (reg al) ++
          movzbq (reg al) r10

      | Bne ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          setne (reg al) ++
          movzbq (reg al) r10

      | Blt ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          setl (reg al) ++
          movzbq (reg al) r10

      | Ble ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          setle (reg al) ++
          movzbq (reg al) r10

      | Bgt ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          setg (reg al) ++
          movzbq (reg al) r10

      | Bge ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          cmpq (reg r10) (reg r11) ++
          setge (reg al) ++
          movzbq (reg al) r10
      end

  | TEblock es ->
      iter expr es

  | TEprint es ->
      let rec go = function
        | [] -> nop
        | [p] -> emit_print_one p
        | p :: q :: rest ->
            let sep =
              if is_atom_like p.expr_typ && is_atom_like q.expr_typ
              then emit_space
              else nop
            in
            emit_print_one p ++ sep ++ go (q :: rest)
      in
      go es

  | TEvars _ ->
      nop

  | TEassign _ ->
      failwith "expr: assignment should be handled by stmt"

  | TEif _ ->
      failwith "expr: if should be handled by stmt"

  | TEfor _ ->
      failwith "expr: for should be handled by stmt"

  | TEreturn _ ->
      failwith "expr: return should be handled by stmt"

  | TEincdec _ ->
      failwith "expr: incdec not implemented yet"

  | TEcall (fn, args) ->
      let asm_name = if fn.fn_name = "main" then "go_main" else fn.fn_name in
      let push_args =
        iter (fun a -> expr a ++ pushq (reg r10)) (List.rev args)
      in
      let cleanup =
        if args = [] then nop
        else addq (imm (8 * List.length args)) (reg rsp)
      in
      push_args ++
      call asm_name ++
      cleanup ++
      movq (reg rax) (reg r10)

  | TEnew ty ->
        let size =
        match ty with
        | Tstruct s -> s.s_size
        | _ -> 8
        in
        movq (imm 1) (reg rdi) ++
        movq (imm size) (reg rsi) ++
        call "calloc_" ++
        movq (reg rax) (reg r10)

(* stmt ret_lbl e:
   generate statement/control-flow code *)
and stmt ret_lbl (e : expr) =
  match e.expr_desc with
  | TEskip ->
      nop

  | TEblock es ->
      iter (stmt ret_lbl) es

  | TEvars _ ->
      nop

  | TEprint _ ->
      expr e

  | TEassign (lhss, rhss) ->
      (* Evaluate all RHS first, store their values on the stack *)
      let eval_rhs =
        iter (fun rhs -> expr rhs ++ pushq (reg r10)) rhss
      in
      let store_one lhs =
        addr lhs ++
        popq r11 ++
        movq (reg r11) (ind r10)
      in
      eval_rhs ++ iter store_one (List.rev lhss)

  | TEincdec (lv, Inc) ->
      addr lv ++
      movq (ind r10) (reg r11) ++
      addq (imm 1) (reg r11) ++
      movq (reg r11) (ind r10)

  | TEincdec (lv, Dec) ->
      addr lv ++
      movq (ind r10) (reg r11) ++
      subq (imm 1) (reg r11) ++
      movq (reg r11) (ind r10)

  | TEif (cond, e_then, e_else) ->
      let l_else = new_label () in
      let l_end  = new_label () in
      expr cond ++
      cmpq (imm 0) (reg r10) ++
      je l_else ++
      stmt ret_lbl e_then ++
      jmp l_end ++
      label l_else ++
      stmt ret_lbl e_else ++
      label l_end

  | TEfor (cond, body) ->
      let l_test = new_label () in
      let l_body = new_label () in
      let l_end  = new_label () in
      label l_test ++
      expr cond ++
      cmpq (imm 0) (reg r10) ++
      jne l_body ++
      jmp l_end ++
      label l_body ++
      stmt ret_lbl body ++
      jmp l_test ++
      label l_end

  | TEreturn es ->
      begin match es with
      | [] ->
          jmp ret_lbl

      | [e1] ->
          expr e1 ++
          movq (reg r10) (reg rax) ++
          jmp ret_lbl

      | _ ->
          failwith "stmt: multiple return values not implemented yet"
      end

  | _ ->
      expr e

let zero_frame frame_size =
  let rec aux ofs =
    if ofs <= 0 then nop
    else
      movq (imm 0) (ind ~ofs:(-ofs) rbp) ++ aux (ofs - 8)
  in
  aux frame_size
let init_addr_taken_vars (fn : function_) (body : expr) =
  let code = ref nop in
  let seen : (int, unit) Hashtbl.t = Hashtbl.create 17 in

  let init_once (v : var) =
    if v.v_addr && v.v_ofs <> -1 && not (Hashtbl.mem seen v.v_id) then begin
      Hashtbl.add seen v.v_id ();
      code :=
        !code ++
        movq (imm 1) (reg rdi) ++
        movq (imm 8) (reg rsi) ++
        call "calloc_" ++
        movq (reg rax) (ind ~ofs:v.v_ofs rbp)
    end
  in

  let rec visit_expr (e : expr) =
    match e.expr_desc with
    | TEskip
    | TEconstant _
    | TEnil -> ()

    | TEident v -> init_once v
    | TEunop (_, e1) -> visit_expr e1
    | TEbinop (_, e1, e2) -> visit_expr e1; visit_expr e2
    | TEnew _ -> ()
    | TEcall (_, args) -> List.iter visit_expr args
    | TEdot (e1, _) -> visit_expr e1
    | TEassign (lhs, rhs) -> List.iter visit_expr lhs; List.iter visit_expr rhs
    | TEvars vars -> List.iter init_once vars
    | TEif (c, e1, e2) -> visit_expr c; visit_expr e1; visit_expr e2
    | TEreturn es -> List.iter visit_expr es
    | TEblock es -> List.iter visit_expr es
    | TEfor (c, b) -> visit_expr c; visit_expr b
    | TEprint es -> List.iter visit_expr es
    | TEincdec (e1, _) -> visit_expr e1
  in

  List.iter init_once fn.fn_params;
  visit_expr body;
  !code
let layout_function (fn : function_) (body : expr) =
  let ofs = ref 0 in

  let alloc_var (v : var) =
    if v.v_ofs = -1 then begin
      ofs := !ofs + 8;
      v.v_ofs <- - !ofs
    end
  in

  let rec visit_expr (e : expr) =
    match e.expr_desc with
    | TEskip
    | TEconstant _
    | TEnil ->
        ()

    | TEident v ->
        alloc_var v

    | TEunop (_, e1) ->
        visit_expr e1

    | TEbinop (_, e1, e2) ->
        visit_expr e1;
        visit_expr e2

    | TEnew _ ->
        ()

    | TEcall (_, args) ->
        List.iter visit_expr args

    | TEdot (e1, _) ->
        visit_expr e1

    | TEassign (lhs, rhs) ->
        List.iter visit_expr lhs;
        List.iter visit_expr rhs

    | TEvars vars ->
        List.iter alloc_var vars

    | TEif (c, e1, e2) ->
        visit_expr c;
        visit_expr e1;
        visit_expr e2

    | TEreturn es ->
        List.iter visit_expr es

    | TEblock es ->
        List.iter visit_expr es

    | TEfor (c, b) ->
        visit_expr c;
        visit_expr b

    | TEprint es ->
        List.iter visit_expr es

    | TEincdec (e1, _) ->
        visit_expr e1
  in

  List.iter alloc_var fn.fn_params;
  visit_expr body;

  let size = !ofs in
  let aligned_size =
    if size mod 16 = 0 then size else size + (16 - size mod 16)
  in
  Hashtbl.replace frame_sizes fn.fn_name aligned_size
let save_params (fn : function_) =
  let rec aux i = function
    | [] -> nop
    | p :: ps ->
        let incoming_ofs = 16 + 8 * i in
        (if p.v_addr then
           (* [rbp + p.v_ofs] contains the pointer to the backing cell *)
           movq (ind ~ofs:p.v_ofs rbp) (reg r10) ++
           movq (ind ~ofs:incoming_ofs rbp) (reg r11) ++
           movq (reg r11) (ind r10)
         else
           movq (ind ~ofs:incoming_ofs rbp) (reg r11) ++
           movq (reg r11) (ind ~ofs:p.v_ofs rbp))
        ++ aux (i + 1) ps
  in
  aux 0 fn.fn_params
let decl = function
  | TDfunction (fn, body) ->
      let asm_name = if fn.fn_name = "main" then "go_main" else fn.fn_name in
      let ret_lbl = new_label () in
      let frame_size =
        match Hashtbl.find_opt frame_sizes fn.fn_name with
        | Some n -> n
        | None -> 0
      in
      label asm_name ++
      pushq (reg rbp) ++
      movq (reg rsp) (reg rbp) ++
      subq (imm frame_size) (reg rsp) ++
      zero_frame frame_size ++
      init_addr_taken_vars fn body ++
      save_params fn ++
      stmt ret_lbl body ++
      label ret_lbl ++
      movq (reg rbp) (reg rsp) ++
      popq rbp ++
      ret

  | TDstruct _ ->
      nop


let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
  Hashtbl.add stringToLabel "%ld" "INT_PRINTER";
  Hashtbl.add stringToLabel " " "SPACE_STR";
  Hashtbl.add stringToLabel "true" "TRUE_STR";
  Hashtbl.add stringToLabel "false" "FALSE_STR";
  Hashtbl.add stringToLabel "<nil>" "NIL_STR";
  Hashtbl.add stringToLabel "%p" "PTR_PRINTER";

  List.iter
    (function
      | TDfunction (fn, body) -> layout_function fn body
      | TDstruct _ -> ())
    dl;

  let all_code = iter decl dl in

  { text =
      globl "main" ++
      label "main" ++
      call "go_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      all_code ++
      inline {|
print_bool_r10:
    cmpq  $0, %r10
    je    .L_false

    leaq  TRUE_STR(%rip), %rdi
    xorl  %eax, %eax
    call  printf_
    ret

.L_false:
    leaq  FALSE_STR(%rip), %rdi
    xorl  %eax, %eax
    call  printf_
    ret

string_eq_r11_r10:
    movq  %r11, %rdi
    movq  %r10, %rsi
    call  strcmp_
    cmpl  $0, %eax
    sete  %al
    movzbq %al, %r10
    ret
|}
      ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
      ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
      ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
      ++ aligned_call_wrapper ~f:"puts" ~newf:"puts_"
      ++ aligned_call_wrapper ~f:"strcmp" ~newf:"strcmp_"
    ;

    data =
      Hashtbl.fold
        (fun str lab acc -> acc ++ label lab ++ string str)
        stringToLabel
        nop
  }