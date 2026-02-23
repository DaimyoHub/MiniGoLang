
open Format
open Lexing
open Lexer
open Parser

let usage = "usage: astform file.go\n"

let report_loc (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol in
  let lc = e.pos_cnum - b.pos_bol in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
  if Array.length Sys.argv <> 2 then (eprintf usage; exit 1) else
  
  let c = open_in Sys.argv.(1) in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.next_token lb in
    pp_ast f;
    close_in c;
  with
    | Lexer.Lexing_error s ->
	      report_loc (lexeme_start_p lb, lexeme_end_p lb);
	      eprintf "lexical error: %s\n@." s;
	      exit 1
    | Parser.Error | Parsing.Parse_error ->
	      report_loc (lexeme_start_p lb, lexeme_end_p lb);
	      eprintf "syntax error\n@.";
	      exit 1
    | e ->
	      eprintf "Anomaly: %s\n@." (Printexc.to_string e);
	      exit 2

let pp_ast 

