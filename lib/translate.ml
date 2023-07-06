open Ast
open List

let join_with s list = 
  let rec aux str = function
  | [] -> str
  | x :: t -> match str with 
  | "" -> aux x t
  | _ -> aux (str ^ s ^ x) t
in aux "" list

(* let map f a = 
  let rec aux b = function
  | [] -> b
  | x :: t -> aux ((f x) :: b) t
in aux [] (List.rev a);; *)

let rec term_translate = function
| Symbol x -> let sym = match x with 
  | "false" -> "⊥"
  | "true" -> "⊤"
  | _ -> x in sym
| Const c -> let string_of_const = function | Numeral y -> string_of_int y | String y -> y in 
  string_of_const c
| Not t -> "¬ " ^ term_translate t
| Or list -> "(" ^ join_with " ∨c " (map term_translate list) ^ ")"
| And list -> "(" ^ join_with " ∧c " (map term_translate list) ^ ")"
| Equal (l, r) -> "(" ^ term_translate l ^ " = " ^ term_translate r ^ ")"
| _ -> "TODO"

(* let rec merge = 
  let rec merge_two_lists a b = 
    let rec is_it_in list n = match list with 
    | [] -> false
    | x :: t -> if x = n then true else is_it_in t n in 
  match b with 
  | [] -> a
  | x :: t -> if is_it_in a x then merge_two_lists a t else merge_two_lists (a @ [x]) t in
  function
| [] -> []
| [] :: t -> merge t
| [a] -> a
| a :: b :: t -> merge ((merge_two_lists a b) :: t) *)

(* let rec get_subsymbols = function
| Symbol x -> [x]
| Const c -> let string_of_const = function | Numeral y -> string_of_int y | String y -> y in
  [string_of_const c] (*do something else for the constants*)
| Not t -> get_subsymbols t
| Or list | And list -> merge (map get_subsymbols list)
| Equal (l, r) -> merge [get_subsymbols l; get_subsymbols r]
| _ -> ["TODO"] *)

exception SyntaxError of string
exception SemanticError of string
exception UnderConstruction of string

(* returns the index of el in list *)
let rec find_idx el = function 
| [] -> raise Not_found
| x :: t -> if x = el then 0 else 1 + find_idx el t 
(* let find_idx el list = List.find 
  (function | -1 -> false | _ -> true)
  (
    List.mapi (fun i r -> if r = el then i else -1) list
  ) *)

let rec get_str_n str = function 
| 0 -> ""
| n -> str ^ get_str_n str (n - 1)


let rule_and_simplify x y = 
  match x with 
  | Ast.And xlist -> let lpi_proof = match y with 
    | Ast.And _ -> raise (UnderConstruction "kindly wait")  (*TODO -- proof for removing duplicates*)
    | Ast.Symbol "false" -> let rec get_contradicting_formulae = function 
      | [_] | [] -> raise (SemanticError "there is no contradiction in LHS for RHS to be 'false'")
      | x :: t -> let rec aux1 = function 
        | Ast.Not z -> let p, fi = aux1 z in (1 + p, fi)
        | z -> (0, z) in
        let rec aux2 (p, f) = function 
        | z :: t -> let (q, g) = aux1 z in 
          if (f = g) && ((p + q) mod 2 = 1) then Some (q, z) else aux2 (p, f) t
        | [] -> None in 
        let (p, f) = aux1 x in
        match aux2 (p, f) t with 
        | None -> get_contradicting_formulae t
        | Some (q, z) -> (x, p, z, q) in 
      let (x, j1, z, j2) = get_contradicting_formulae xlist in 
      let (f1, f2, i1, i2) = if j1 < j2 then (x, z, j1, j2) else (z, x, j2, j1) in 
      let f1i = find_idx f1 xlist in
      let f2i = find_idx f2 xlist in 
      let t = term_translate (Ast.And xlist) in 
      let f1_header = get_str_n "∧e2c _ _ (" f1i ^ " h3 " ^ get_str_n ")" f1i in
      let f2_header = get_str_n "∧e2c _ _ (" f2i ^ " h3 " ^ get_str_n ")" f2i in 
      let l_xlist = List.length xlist in
      let f1_refine = if f1i = l_xlist - 1 then " {refine " else " {refine ∧e1c _ _ (" in
      let f2_refine = if f2i = l_xlist - 1 then " {refine " else " {refine ∧e1c _ _ (" in
      let f2_end = if f2i = l_xlist - 1 then ";};\n" else ");};\n" in 
      let f1_end = if f1i = l_xlist - 1 then ";};\n" else ");};\n" in 
      let have_f1 = "have f1 : Prfc " ^ term_translate f1 ^ f1_refine ^ f1_header ^ f1_end in 
      let have_f2 = "have f2 : Prfc " ^ term_translate f2 ^ f2_refine ^ f2_header ^ f2_end in
      let aux_foo str n = 
        let sn = string_of_int n in 
        str ^ "assume f2_" ^ sn ^ "; refine f2_" ^ sn ^ " _; \n" in 
      let h1_footer = List.fold_left aux_foo "refine f2 _; \n" (List.init ((i2 - i1) / 2) (fun r -> r + 1)) ^ "refine f1; \n" in
      let h1_header = "have h1 : Prf (" ^ t ^ " ⇒c ⊥) {\nassume h3;\nassume nf;\nrefine h3 _;\nassume h4;\n" in 
      let h1_body = h1_header ^ have_f1 ^ have_f2 ^ h1_footer ^ "};\n" in 
      let h2_body = "have h2 : Prf (⊥ ⇒c " ^ t ^ ") {\nassume nnf; apply ⊥e; apply nnf; assume pf; refine pf;};\n" in 
      let proof_header = "Prfc (" ^ t ^ "=c ⊥) ≔ begin \nassume nh;\nrefine nh _;\n" in 
      let proof_footer = "assume s1 left1;\napply left1 h1 h2;\nend;\n" in 
      proof_header ^ h1_body ^ h2_body ^ proof_footer
    | Ast.Symbol "true" -> raise (UnderConstruction "kindly wait") (*TODO*)
    | _ -> raise (SyntaxError "RHS of the equality is of an unexpected type")
    in lpi_proof
  | _ -> raise (SyntaxError "LHS of the equality must be of type Ast.And")


let step_translate cl rule premises =
  match rule with 
  | "and_simplify" -> let lpi_proof = match cl with 
    | [Ast.Equal (x, y)] -> rule_and_simplify x y
    | _ -> raise (SyntaxError "expected a clause with only one literal of type Ast.Equal")
    in lpi_proof
  | "th_resolution" -> let lpi_proof = match premises with 
    | None -> raise (SyntaxError "need premises for this rule")
    | Some (Ast.Annotation _) -> "/* TODO */"
    | _ -> raise (SyntaxError "premises must be of type Ast.Annotation")
    in lpi_proof 
  | "equiv_pos2" -> "/* TODO */"
  | "false" -> "/* TODO */"
  | "" -> raise (SyntaxError "missing rule")
  | _ -> "/* TODO */"

let get_lp_commands = function
| Assume x -> "symbol " ^ x.name ^ " ≔ Prfc (" ^ term_translate x.term ^ ");"   (* ≔ *)
| Step x -> let proof_def =
  match step_translate x.clause x.rule x.annotations with 
  | "/* TODO */" -> "/* TODO */" 
  | lp_proof -> "symbol " ^ x.name ^ " : " ^ lp_proof in 
  proof_def
| _ -> "/* TODO */"

let rec get_lp_script = function
| [] -> ""
| x :: t -> (get_lp_commands x) ^ "\n" ^ get_lp_script t

