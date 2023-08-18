open Smtlib_utils.V_2_6.Ast

exception UnderConstruction of string

let smt2lp_stmt out (st : statement) =
  match view st with
  | Stmt_set_info (_, _) -> fpf out ""
  | Stmt_set_logic s ->
      let pp_set_logic =
        match s with
        | "QF_UF" -> fpf out "require open lfroma.qfuf_encoding ; \n"
        | _ ->
            raise
              (UnderConstruction "The following logic is not yet supported.")
      in
      pp_set_logic
  | Stmt_set_option _ -> fpf out ""
  | Stmt_decl_sort (s, n) ->
      let pp_decl_sort =
        match n with
        | 0 -> fpf out "constant symbol %s : TYPE;" s
        | _ ->
            raise
              (UnderConstruction "Parameterized sort are not yet supported.")
      in
      pp_decl_sort
  | Stmt_assert _ -> fpf out ""
  | Stmt_decl d ->
      if d.fun_ty_vars = [] then
        fpf out "symbol %s : Term %a ; \n" d.fun_name pp_ty d.fun_ret
      else raise (UnderConstruction "I don't know what to do in this case")
  | Stmt_fun_def fr ->
      fpf out "(@[<2>define-fun@ %a@])" (pp_par pp_fr)
        (fr.fr_decl.fun_ty_vars, fr)
  | Stmt_fun_rec fr ->
      fpf out "(@[<2>define-fun-rec@ %a@])" (pp_par pp_fr)
        (fr.fr_decl.fun_ty_vars, fr)
  | Stmt_funs_rec fsr ->
      let pp_decl' out d = fpf out "(@[<2>%a@])" (pp_fun_decl pp_typed_var) d in
      fpf out "(@[<hv2>define-funs-rec@ (@[<v>%a@])@ (@[<v>%a@])@])"
        (pp_list pp_decl') fsr.fsr_decls (pp_list pp_term) fsr.fsr_bodies
  | Stmt_data _ -> fpf out "/* TODO */"
  | _ -> fpf out ""
