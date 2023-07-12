open Ast

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
| Or list -> "(" ^ join_with " ∨c " (List.map term_translate list) ^ ")"
| And list -> "(" ^ join_with " ∧c " (List.map term_translate list) ^ ")"
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

(* let rec get_str_n str = function 
| 0 -> ""
| n -> str ^ get_str_n str (n - 1) *)

let l_prf x = "Prf " ^ x 
let l_prfc x = "Prfc " ^ x
let l_assume x = "assume " ^ join_with " " x ^ "; "
let l_refine  x = "refine " ^ join_with " " x ^ "; "
let l_apply x = "apply " ^ join_with " " x ^ "; "
let l_have (x : string) (proof : string) (list : string list) : string = 
  "have " ^ x ^ " : " ^ proof ^ " { \n" ^ join_with "\n" list ^ "};\n"
let l_app x y = x ^ " (" ^ y ^ ")"
let l_proof_statement proof list = proof ^ " ≔ begin \n" ^ 
  join_with " \n" list ^ " \nend;\n"
let ltop = "Τ"
let lbot = "⊥"
let lnot = "¬"

let apply_n_times (n : int) (app_str : string) (init_str : string) : string = 
  List.fold_left (fun y _ -> l_app app_str y) init_str (List.init n (fun _ -> 0))

let rec not_counter = function 
| Not z -> let (p, fi) = not_counter z in (1 + p, fi) 
| z -> (0, z)

let rule_and_simplify x y = 
  match x with 
  | Ast.And xlist -> let len_xlist = List.length xlist in 
  let t = term_translate (And xlist) in
  let lpi_proof = match y with 
    | Ast.And _ -> raise (UnderConstruction "why am I so lazy??")  (*TODO -- proof for removing duplicates*)
    | Ast.Symbol "false" -> let rec get_contradicting_formulae = function 
      | [_] | [] -> raise (SemanticError "there is no contradiction in LHS for RHS to be 'false'")
      | x :: tl -> let rec aux2 (p, f) = function 
        | z :: sl -> let (q, g) = not_counter z in 
          if (f = g) && ((p + q) mod 2 = 1) then Some (q, z) else aux2 (p, f) sl
        | [] -> None in 
        let (p, f) = not_counter x in
        match aux2 (p, f) tl with 
        | None -> get_contradicting_formulae tl
        | Some (q, z) -> (x, p, z, q) in 
      let rec check_false i = function 
      | [] -> None
      | x :: tl -> let (p, f) = not_counter x in 
        if f = Symbol "false" && p mod 2 = 0 then Some (p, f, i) else check_false (i + 1) tl in 
      let proof_of_contradiction = match check_false 0 xlist with 
      | Some (p, f, i) -> l_proof_statement (l_prfc ("(" ^ t ^ " =c ⊥)"))
        [
          l_assume ["nh"]; l_refine ["nh _"];
          l_have "h1" (l_prf ("(" ^ t ^ " ⇒c ⊥)")) [
            l_assume ["h3"]; l_have "f1" (l_prfc (apply_n_times p lnot (term_translate f))) [
              let selector = apply_n_times i "∧e2c _ _" "h3" in 
              if i = len_xlist - 1 then l_refine [selector] else l_refine [l_app "∧e1c _ _" selector]; 
            ];
            l_refine [apply_n_times (p / 2) "double_neg _" "f1"];
          ];
          l_have "h2" (l_prf ("(⊥ ⇒c " ^ t ^ ")")) [
            l_assume ["nnf"]; l_apply ["⊥e"]; l_apply ["nnf"];
            l_assume ["pf"]; l_refine ["pf"];
          ];
          l_assume ["s1"; "left1"]; l_apply ["left1"; "h1"; "h2"]
        ]
      | None -> 
      let (x, j1, z, j2) = get_contradicting_formulae xlist in 
      let (f1, f2, i1, i2) = if j1 < j2 then (x, z, j1, j2) else (z, x, j2, j1) in 
      let f1i = find_idx f1 xlist in
      let f2i = find_idx f2 xlist in 
      let f1_header = List.fold_left (fun y _ -> l_app "∧e2c _ _" y) "h3" (List.init f1i (fun _ -> 0)) in 
      let f2_header = List.fold_left (fun y _ -> l_app "∧e2c _ _" y) "h3" (List.init f2i (fun _ -> 0)) in
      (* let len_xlist = List.length xlist in *)
      let have_f1 = l_have "f1" (l_prfc (term_translate f1)) 
        [if f1i = len_xlist - 1 then l_refine [f1_header] else l_refine [l_app "∧e1c _ _" f1_header]] in
      let have_f2 = l_have "f2" (l_prfc (term_translate f2)) 
        [if f2i = len_xlist - 1 then l_refine [f2_header] else l_refine [l_app "∧e1c _ _" f2_header]] in
      let aux_foo str n = 
        let sn = string_of_int n in 
        str ^ l_assume ["f2_" ^ sn] ^ l_refine ["f2_" ^ sn; "_"] ^ "\n" in 
      let h1_footer = List.fold_left aux_foo "refine f2 _; \n" (List.init ((i2 - i1) / 2) (fun r -> r + 1)) ^ "refine f1; \n" in
      let h1_body = l_have "h1" (l_prf ("(" ^ t ^ " ⇒c ⊥)")) 
        [l_assume ["h3"; "nf"]; l_refine ["h3"; "_"]; l_assume ["h4"]; have_f1; have_f2; h1_footer;] in
      let h2_body = l_have "h2" (l_prf ("(⊥ ⇒c " ^ t ^ ")")) 
        [l_assume ["nnf"]; l_apply ["⊥e"]; 
         l_apply ["nnf"]; l_assume ["pf"]; l_refine ["pf"]] in
      l_proof_statement (l_prfc ("(" ^ t ^ " =c ⊥)")) 
        [l_assume ["nh"]; l_refine ["nh"; "_"]; h1_body; h2_body; 
         l_assume ["s1"; "left1"]; l_apply ["left1"; "h1"; "h2"]] in 
      proof_of_contradiction
    | Ast.Symbol "true" -> let rec truth_counter = function 
      | [] -> 0 
      | x :: t -> (if x = Symbol "true" then 1 else 0) + truth_counter t in
      if len_xlist <> (truth_counter xlist) then raise (SemanticError ("Can't equate the LHS to " ^ ltop)) else 
         l_proof_statement (l_prfc "(" ^ t ^ " =c " ^ ltop ^ ")") [
          l_assume ["nh"]; l_refine ["nh _"]; 
          l_have "h1" (l_prf ("(" ^ t ^ " ⇒c " ^ ltop ^ ")")) [
            l_assume ["h3"; "nt"]; l_refine ["∧e1c _ _ h3 nt"];
          ];
          l_have "h2" (l_prf ("(" ^ ltop ^ " ⇒c " ^ t ^ ")")) [
            l_assume ["pt"];
            l_refine [List.fold_left (fun y _ -> l_app "∧ic _ _" y) "pt" (List.init (len_xlist - 1) (fun _ -> 0))]
          ];
          l_assume ["s1"; "left1"];
          l_apply ["left1"; "h1"; "h2"] 
         ]
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

