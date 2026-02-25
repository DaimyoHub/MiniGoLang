open Ast
open Lib

module Struct = struct
  let rec ptyp_well_defined struct_list = function
    | PTident ident -> List.mem ident.id struct_list
    | PTptr ptyp -> ptyp_well_defined struct_list ptyp
    
  let naive_check_deps decls =
    let struct_list =
      List.fold_left
        (fun acc -> function
         | PDfunction _ -> acc
         | PDstruct strc -> strc.ps_name.id :: acc)
        []
        decls
    in

    List.for_all
      (function
       | PDfunction _ -> true
       | PDstruct strc ->
           List.for_all
             (fun (_, field_ptyp) -> ptyp_well_defined struct_list field_ptyp)
             strc.ps_fields)
      decls
end
