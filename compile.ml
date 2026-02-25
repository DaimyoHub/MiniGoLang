(** Code generation for Mini Go programs (TODO) *)

open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

let stringToLabel : (string, string) Hashtbl.t = Hashtbl.create 5


let rec expr = function
| { expr_desc = desc;
    expr_typ  = ty; } -> 
      pexpr_desc desc
and  is_int_or_bool = function
  | Tint | Tbool -> true
  | _ -> false

and emit_print_one p =
  expr p ++ xorq (reg rax) (reg rax) ++
  match p.expr_typ with
  | Tstring ->
      movq (reg r10) (reg rdi) ++ call "printf"
  | Tint ->
      movq (reg r10) (reg rsi) ++ movq (ilab "INT_PRINTER") (reg rdi) ++ call "printf"
  | Tbool ->
      call "print_bool_r10"
  | _ ->
      failwith "Unsupported type in print"

and emit_space =
  movq (ilab "SPACE_STR") (reg rdi) ++ xorq (reg rax) (reg rax) ++ call "printf"

and pexpr_desc = function (* Generates code to compute expression and stores it in r10*)
  | TEconstant (Cstring s) -> 
    let lab = new_label () in
    Hashtbl.add stringToLabel s lab;
    movq (ilab lab) (reg r10)
  | TEbinop (op, e1, e2) ->
    (match op with
      | Badd ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          addq (reg r11) (reg r10)
      | Bsub ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
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
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          andq (reg r11) (reg r10)
      | Bor ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq r11 ++
          orq (reg r11) (reg r10)
          
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
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++ 
          sete (reg al) ++
          movzbq (reg al) (r10)

      | Bne ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++
          setne (reg al) ++
          movzbq (reg al) (r10)
      | Blt ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++ 
          setl (reg al) ++
          movzbq (reg al) (r10)

      | Ble ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++
          setle (reg al) ++
          movzbq (reg al) (r10)

      | Bgt ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++
          setg (reg al) ++
          movzbq (reg al) (r10)

      | Bge ->
          expr e1 ++ pushq (reg r10) ++
          expr e2 ++ popq (r11) ++
          cmpq (reg r10) (reg r11) ++
          setge (reg al) ++
          movzbq (reg al) (r10)
      | _ -> failwith "Unsupported binary operator")
  | TEconstant (Cint n) -> movq (ilab (Int64.to_string n)) (reg r10)
  | TEconstant (Cbool b) -> 
    (match b with 
      | true -> movq (ilab "1") (reg r10)
      | false -> movq (ilab "0") (reg r10))

  | TEblock ls -> iter expr ls
  | TEprint l ->
      let rec go = function
        | [] -> nop
        | [p] -> emit_print_one p
        | p :: q :: rest ->
            let sep =
              if is_int_or_bool p.expr_typ && is_int_or_bool q.expr_typ
              then emit_space
              else nop
            in
            emit_print_one p ++ sep ++ go (q :: rest)
          in go l
  |_ -> failwith "Later"


let decl = function 
| TDfunction ({
  fn_name = fname;
  fn_params = ps;
     fn_typ = ts;}, exp) -> label fname ++ expr exp
|_ -> failwith "Later"

let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
  Hashtbl.add stringToLabel "%d" "INT_PRINTER";
  Hashtbl.add stringToLabel " " "SPACE_STR";
  Hashtbl.add stringToLabel "true" "TRUE_STR";
  Hashtbl.add stringToLabel "false" "FALSE_STR";
  let mainValue = decl (List.hd dl) in
  { text =
      globl "main" ++ 
      mainValue (* TODO call Go main function here *) ++
      xorq (reg rax) (reg rax) ++
      ret ++
      nop (* TODO assembly code for the Go functions here *) ++
inline {|
# TODO some auxiliary assembly functions, if needed
print_bool_r10:
    cmpq  $0, %r10
    je    .L_false

    # r10 != 0 → print "true"
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
      Hashtbl.fold (fun str lab acc -> acc ++ (label lab) ++ (string str)) stringToLabel nop (* TODO static data here, such as string constants *)
    ;
  }