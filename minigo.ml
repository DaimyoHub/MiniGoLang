
open Format
open Lexing
open Lexer
open Ast
open Parser
open Error

let usage = "usage: minigo [options] file.go"

let debug = ref false
let parse_only = ref false
let type_only = ref false
let show_ast = ref false

let spec =
  [ "--debug", Arg.Set debug, "  runs in debug mode";
    "--parse-only", Arg.Set parse_only, "  stops after parsing";
    "--type-only", Arg.Set type_only, "  stops after typing";
    
    "--show-ast", Arg.Set show_ast, "  show the Abstract Syntax Tree"
  ]

let file =
  let file = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".go") then
      raise (Arg.Bad "no .go extension");
    file := Some s
  in
  Arg.parse spec set_file usage;
  match !file with Some f -> f | None -> Arg.usage spec usage; exit 1

let debug = !debug
let type_only = !type_only

let report_loc (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol in
  let lc = e.pos_cnum - b.pos_bol in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc


let pp_ast ((import_fmt, tu): Ast.pfile) =
  let rec string_of_ptyp =
    function
    | PTident ident -> ident.id
    | PTptr t -> "*" ^ (string_of_ptyp t)
  in
  if import_fmt then printf "import fmt\n";

  List.iter
    (function
    | PDfunction func ->
        begin
          printf "Function %s {\n" func.pf_name.id;
          (************)
          printf "\tparams => ";
          List.iter
            (fun (p_ident, p_typ) ->
              printf "%s: %s; " p_ident.id (string_of_ptyp p_typ))
            func.pf_params;
          printf "\n";
          (************)
          printf "\ttype => ";
          List.iter (fun t -> printf "%s; " (string_of_ptyp t)) func.pf_typ;
          printf "\n";
          printf "}\n"
        end
    | PDstruct strc -> ())
    tu

let string_of_err = function
  | Lhs                 -> "Left hand side is ill typed."
  | Rhs                 -> "Right hand side is ill typed."
  | Binop               -> "Binary expression is ill typed."
  | Unop                -> "Unary expression is ill typed."
  | Func_not_found      -> "Function was not found."
  | Struct_not_found    -> "Structure was not found."
  | Several_funcs       -> "Found several definitions of the same function."
  | Several_structs     -> "Found several definitions of the same structure."
  | Main_not_found      -> "Entry point 'main' was not found. It is mandatory to define it."
  | Calling_main        -> "Trying to call 'main' function."
  | Arity               -> "Found an arity inconsistance."
  | Mismatch            -> "Found a type mismatch."
  | For_branch          -> "Body of the for loop is ill typed."
  | If                  -> "Conditional is ill typed."
  | If_branch           -> "Positive branch of the conditional is ill typed."
  | Else_branch         -> "Negative branch of the conditional is ill typed."
  | Params              -> "Found an inconsistance in parameters' types."
  | Args                -> "Arguments are ill typed."
  | Lvalues             -> "Found an inconsistance in lvalues' types."
  | Rvalues             -> "Rvalues are ill typed."
  | Var                 -> "Found an inconsistance in variable type."
  | Block               -> "Block is ill typed."
  | Return              -> "Return instruction is ill typed."
  | Cond                -> "Condition is ill typed."
  | Ident               -> "Found an inconsistance in identifier's type."
  | Assignments         -> "Assignements are ill typed."
  | Incdec              -> "Unary expression is ill typed."
  | Var_not_found       -> "Variable was not found."
  | Field_not_found     -> "Field was not found."
  | Unknown_typ         -> "Unknown type."
  | Object              -> "Expected object before dot."
  | Dot                 -> "Dot expression is ill typed."
  | New                 -> "New expression is ill typed."
  | Invalid_typ         -> "Found an invalid type."
  | Fmt_import_not_used -> "Imported module 'fmt' is not used."
  | Dummy               -> ""

let string_of_loc (loc : Ast.location) : string =
  let (start, stop) = loc in
  Printf.sprintf "line %d, characters %d-%d"
    start.pos_lnum
    (start.pos_cnum - start.pos_bol)
    (stop.pos_cnum  - stop.pos_bol)

let parse_type_error_report (r : rep) : string =
  let rec clean_report r =
    let rec remove x =
      function
      | Rep (b, loc, rest) ->
          if x = b then remove x rest else Rep (b, loc, remove x rest)
      | Nil -> Nil
    in
    match r with
    | Rep (a, loc, rest) -> Rep (a, loc, clean_report (remove a rest))
    | Nil -> Nil
  in
  let rec loop = function
    | Rep (err, loc, rest) ->
        loop rest ^
          (if err = Dummy then "" else
            "  -> " ^ (string_of_err err) ^
            (if loc = dummy_loc then "\n"
             else " (" ^ string_of_loc loc ^ ")\n"))
    | Nil -> ""
  in loop (clean_report r)

let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.next_token lb in
    close_in c;
    if !show_ast then (pp_ast f; exit 0);
    if !parse_only then exit 0;
    let f = Typing.file ~debug f in
    if type_only then exit 0;
    let f = Rewrite.file ~debug f in
    if debug then eprintf "%a@." Pretty.file f;
    let code = Compile.file ~debug f in
    let c = open_out (Filename.chop_suffix file ".go" ^ ".s") in
    let fmt = formatter_of_out_channel c in
    X86_64.print_program fmt code;
    close_out c
  with
    | Lexer.Lexing_error s ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "lexical error: %s\n@." s;
	exit 1
    | Parser.Error | Parsing.Parse_error ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "syntax error\n@.";
	exit 1
    | Typing.Err (l, rep) ->
	report_loc l;
	eprintf "error: \n%s\n@." (parse_type_error_report rep);
	exit 1
    | e ->
	eprintf "Anomaly: %s\n@." (Printexc.to_string e);
	exit 2
