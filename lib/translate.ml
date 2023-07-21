open Ast
module H = Helper

type l_term = string 

exception SyntaxError of string
exception SemanticError of string
exception UnderConstruction of string  (*used while working on the code*)

let rec term_translate = function
| Symbol x -> let sym = match x with 
  | "false" -> "⊥"
  | "true" -> "⊤"
  | _ -> x in sym
| Const c -> let string_of_const = function | Numeral y -> string_of_int y | String y -> y in 
  string_of_const c
| Not t -> "¬ " ^ term_translate t
| Or list -> "(" ^ H.join_with " ∨c " (List.map term_translate list) ^ ")"
| And list -> "(" ^ H.join_with " ∧c " (List.map term_translate list) ^ ")"
| Xor list -> "(" ^ H.join_with " xorc " (List.map term_translate list) ^ ")"
| Equal (l, r) -> "(" ^ term_translate l ^ " =c " ^ term_translate r ^ ")"
| Implies (l, r) -> "(" ^ term_translate l ^ " ⇒c " ^ term_translate r ^ ")"
| _ -> "TODO"

let l_prf (x : l_term) : l_term = "Prf " ^ x 
let l_prfc (x : l_term) : l_term = "Prfc " ^ x
let l_assume (x : l_term list) : l_term = "assume " ^ H.join_with " " x ^ "; "
let l_refine  (x : l_term list) : l_term = "refine " ^ H.join_with " " x ^ "; "
let l_apply (x : l_term list) : l_term = "apply " ^ H.join_with " " x ^ "; "
let l_have (x : l_term) (ltype : l_term) (list : l_term list) : l_term = 
  "have " ^ x ^ " : " ^ ltype ^ " { \n" ^ H.join_with "\n" list ^ "};\n"
let l_app (x : l_term) (y : l_term) : l_term = x ^ " (" ^ y ^ ")"
let l_proof_statement (ltype : l_term) (list : l_term list) : l_term = 
  (*returns the type and its proof*)
  ltype ^ " ≔ begin \n" ^ H.join_with " \n" list ^ " \nend;\n"
let ltop = "⊤"
let lbot = "⊥"
let lnot = "¬"
let limpliesc x y = 
  "(" ^ x ^ " ⇒c " ^ y ^ ")"
let leqc x y = 
  "(" ^ x ^ " =c " ^ y ^ ")"

let apply_n_times (n : int) (app : l_term) (init0 : l_term) : l_term =
  (*returns app (app (... n times ... app ( init0 )))*) 
  List.fold_left (fun y _ -> l_app app y) init0 (List.init n (fun _ -> 0))

let rec not_counter = function
(*checks the number of 'Not's in an alethe term;
  returns that number and the outer-most term that is not a 'Not'*)
| Not z -> let (p, fi) = not_counter z in (1 + p, fi) 
| z -> (0, z)

let and_repetition_remover (xlist : term list) (ylist : term list): string = 
  (*returns the proof of Prfc (And (xlist) =c And (ylist)), 
    where ylist has all repetitions removed and  
    by first getting the proofs for implication in both directions *)
  let len_xlist = List.length xlist in
  let len_ylist = List.length ylist in
  let xt = term_translate (And xlist) in 
  let yt = term_translate (And ylist) in
  (*First, get proof of Prf (xt ⇒c yt)*)
  let indices = List.map (function | None -> -1 | Some i -> i) (H.get_indices ylist xlist) in 
  let have_ith_element_of_ylist_from_xlist hyp_name i p = 
    l_have ("a" ^ string_of_int i) (l_prfc (term_translate (List.nth ylist i))) [
      let selector = apply_n_times p "∧e2c _ _" hyp_name in 
      if p = len_xlist - 1 then l_refine [selector] else l_refine [l_app "∧e1c _ _" selector]] in
  (*have ai : Prfc (ith element of ylist) {...};*)
  let have_elements_of_ylist hyp_name = List.mapi (have_ith_element_of_ylist_from_xlist hyp_name) indices in
  let have_yt = List.fold_right (fun p x -> l_app ("∧ic _ _ a" ^ string_of_int p) x) (List.init (len_ylist - 1) Fun.id) ("a" ^ string_of_int (len_ylist - 1)) in
  let have_xt_implies_yt = l_have "h1" (l_prf (limpliesc xt yt)) 
    ([l_assume ["g0"]] @ (have_elements_of_ylist "g0") @ [l_refine [have_yt]]) in
  (*Now, get proof of Prf (yt ⇒c xt)*)
  let orig_indices = List.map (function | None -> len_ylist | Some i -> i) (H.get_indices xlist ylist) in 
  let indices2 = H.rem_el len_ylist (H.unique_list (orig_indices)) in 
  let have_ith_element_of_ylist_from_ylist hyp_name i = 
    l_have ("a" ^ string_of_int i) (l_prfc (term_translate (List.nth ylist i))) [
      let selector = apply_n_times i "∧e2c _ _" hyp_name in 
      if i = len_ylist - 1 then l_refine [selector] else l_refine [l_app "∧e1c _ _" selector]] in 
  let have_elements_of_ylist_from_ylist hyp_name = List.map (have_ith_element_of_ylist_from_ylist hyp_name) indices2 in
  let have_xt = List.fold_right (fun p x -> l_app ("∧ic _ _ a" ^ string_of_int p) x) (H.elim_last orig_indices) ("a" ^ string_of_int (List.hd (List.rev orig_indices))) in
  let have_yt_implies_xt = l_have "h2" (l_prf (limpliesc yt xt)) ([l_assume ["k0"]] @ (have_elements_of_ylist_from_ylist "k0") @ 
    [l_have ("a" ^ string_of_int (len_ylist)) (l_prfc ltop) [l_refine ["intuition _"; "true"]];
    l_refine [have_xt]]) in
  (*Final step*)
  l_proof_statement (l_prfc (leqc xt yt)) [
    l_assume ["nh"]; l_refine ["nh _"]; have_xt_implies_yt; have_yt_implies_xt;
    l_assume ["s1"; "left1"]; l_apply ["left1"; "h1"; "h2"]
  ]

let rule_and_simplify x y = 
  match x with 
  | And xlist -> let len_xlist = List.length xlist in 
  let t = term_translate (And xlist) in
  let lpi_proof = match y with 
    | And ylist -> and_repetition_remover xlist ylist
    | Symbol "false" -> let rec get_contradicting_formulae = function 
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
      (*check if ⊥ is in xlist*)
      | Some (p, f, i) -> l_proof_statement (l_prfc (leqc t lbot))
        [
          l_assume ["nh"]; l_refine ["nh _"];
          l_have "h1" (l_prf (limpliesc t lbot)) [
            l_assume ["h3"]; l_have "f1" (l_prfc (apply_n_times p lnot (term_translate f))) [
              let selector = apply_n_times i "∧e2c _ _" "h3" in 
              if i = len_xlist - 1 then l_refine [selector] else l_refine [l_app "∧e1c _ _" selector]; 
            ];
            l_refine [apply_n_times (p / 2) "double_neg _" "f1"];
          ];
          l_have "h2" (l_prf (limpliesc lbot t)) [
            l_assume ["nnf"]; l_apply ["⊥e"]; l_apply ["nnf"];
            l_assume ["pf"]; l_refine ["pf"];
          ];
          l_assume ["s1"; "left1"]; l_apply ["left1"; "h1"; "h2"]
        ]
      | None -> (*⊥ is not in xlist; we must have two contradicting formulae*)
      let (x, j1, z, j2) = get_contradicting_formulae xlist in 
      (*get x, z from the list such that 
        x = not not ... phi, z = not not ... phi 
        and x ∧ z = ⊥*)
      let (f1, f2, i1, i2) = if j1 < j2 then (x, z, j1, j2) else (z, x, j2, j1) in 
      (*f2 has more 'not's than f1*)
      let f1i = H.find_idx f1 xlist in
      let f2i = H.find_idx f2 xlist in 
      let f1_header = apply_n_times f1i "∧e2c _ _" "h3" in 
      let f2_header = apply_n_times f2i "∧e2c _ _" "h3" in
      (* let len_xlist = List.length xlist in *)
      let have_f1 = l_have "f1" (l_prfc (term_translate f1)) 
        [if f1i = len_xlist - 1 then l_refine [f1_header] else l_refine [l_app "∧e1c _ _" f1_header]] in
      let have_f2 = l_have "f2" (l_prfc (term_translate f2)) 
        [if f2i = len_xlist - 1 then l_refine [f2_header] else l_refine [l_app "∧e1c _ _" f2_header]] in
      let aux_foo str n = 
        let sn = string_of_int n in 
        str ^ l_assume ["f2_" ^ sn] ^ l_refine ["f2_" ^ sn; "_"] ^ "\n" in 
      let h1_footer =
        (*final steps for obtaining contradiction (⊥)*) 
        List.fold_left aux_foo "refine f2 _; \n" (List.init ((i2 - i1) / 2) (fun r -> r + 1)) ^ "refine f1; \n" in
      (*finishing the proof*)
        l_proof_statement (l_prfc (leqc t lbot)) 
        [l_assume ["nh"]; l_refine ["nh"; "_"]; 
        l_have "h1" (l_prf (limpliesc t lbot)) 
          [l_assume ["h3"; "nf"]; l_refine ["h3"; "_"]; 
          l_assume ["h4"]; have_f1; have_f2; h1_footer;]; 
        l_have "h2" (l_prf (limpliesc lbot t)) 
          [l_assume ["nnf"]; l_apply ["⊥e"]; 
          l_apply ["nnf"]; l_assume ["pf"]; l_refine ["pf"]]; 
        l_assume ["s1"; "left1"]; 
        l_apply ["left1"; "h1"; "h2"]] in 
      proof_of_contradiction
    | Symbol "true" -> let rec truth_counter = function 
      | [] -> 0 
      | x :: t -> (if x = Symbol "true" then 1 else 0) + truth_counter t in
      if len_xlist <> (truth_counter xlist) then raise (SemanticError ("Can't equate the LHS to " ^ ltop)) else 
         l_proof_statement (l_prfc (leqc t ltop)) [
          l_assume ["nh"]; l_refine ["nh _"]; 
          l_have "h1" (l_prf (limpliesc t ltop)) [
            l_assume ["h3"; "nt"]; l_refine ["∧e1c _ _ h3 nt"];
          ];
          l_have "h2" (l_prf (limpliesc ltop t)) [
            l_assume ["pt"];
            l_refine [apply_n_times (len_xlist - 1) "∧ic _ _ pt" "pt"]
          ];
          l_assume ["s1"; "left1"];
          l_apply ["left1"; "h1"; "h2"] 
         ]
    | _ -> raise (SyntaxError "RHS of the equality is of an unexpected type")
    in lpi_proof
  | _ -> raise (SyntaxError "LHS of the equality must be of type Ast.And")


let predefined_proof_generator (ast_term : term) (ref : l_term list) : l_term = 
  (*uses predefined lambdapi proofs directly*)
  l_proof_statement (l_prfc @@ term_translate @@ ast_term) [l_refine ref]


let step_translate cl rule premises =
  match rule with 
  | "and_simplify" -> let lpi_proof = match cl with 
    | [Equal (x, y)] -> rule_and_simplify x y
    | _ -> raise (SyntaxError "expected a clause with only one literal of type Ast.Equal")
    in lpi_proof
  | "th_resolution" -> let lpi_proof = match premises with 
    | None -> raise (SyntaxError "need premises for this rule")
    | Some (Annotation _) -> "/* TODO */"
    | _ -> raise (SyntaxError "premises must be of type Ast.Annotation")
    in lpi_proof 
  | "equiv_pos2" -> let lpi_proof = match cl with 
    | [Not (Equal (x, y)); Not a; b] -> if x = a && y = b then
      predefined_proof_generator (Or cl) [rule; "_ _";]
      else raise (SyntaxError "clause is not of the required form") 
    | _ -> raise (SyntaxError "clause is not of the required form")
    in lpi_proof
  | "not_not" -> let lpi_proof = match cl with 
    | [Not (Not (Not (x))); y] -> if x = y then 
      l_proof_statement (l_prfc @@ term_translate @@ (Or cl)) [l_refine ["not_not _ _"]] 
      else raise (SyntaxError "clause is not of the required form") 
    | _ -> raise (SyntaxError "clause is not of the required form")
    in lpi_proof
  | "eq_reflexive" -> let lpi_proof = match cl with 
    | [Equal (x, y)] -> if x = y then 
      l_proof_statement (l_prfc @@ term_translate @@ Equal (x, y)) [l_refine ["eq_reflexive _"]]
      else raise (SyntaxError "")
    | _ -> raise (SyntaxError "")
    in lpi_proof
  | "implies" -> let lpi_proof = match cl, premises with 
    | [Not _; _], Some (Annotation ([premise1], [])) -> predefined_proof_generator (Or cl) [rule; "_ _"; premise1]
    | _ -> raise (SyntaxError "clause or premises are not of the required form") in lpi_proof
  | "not_implies1" | "not_implies2" -> let lpi_proof = match cl, premises with 
    | [phi], Some (Annotation ([premise1], [])) -> predefined_proof_generator phi [rule; "_ _" ;premise1]
    | _ -> raise (SyntaxError "clause or premises are not of the required form") in lpi_proof
  | "equiv1" | "equiv2" | "not_equiv1" | "not_equiv2" 
  | "xor1" | "xor2" | "not_xor1" | "not_xor2" -> let lpi_proof = match cl, premises with 
    | [_; _], Some (Annotation ([premise1], [])) -> predefined_proof_generator (Or cl) [rule; "_ _"; premise1]
    | _ -> raise (SyntaxError "clause or premises are not of the required form") in lpi_proof
  | "implies_neg1" | "implies_neg2" -> let lpi_proof = match cl with 
    | [_; _] -> predefined_proof_generator (Or cl) [rule; "_ _"]
    | _ -> raise (SyntaxError "clause or premises are not of the required form") in lpi_proof
  | "equiv_pos1" | "equiv_neg1" | "equiv_neg2" -> let lpi_proof = match cl with 
    | [_; _; _] -> predefined_proof_generator (Or cl) [rule; "_ _"]
    | _ -> raise (SyntaxError "clause or premises are not of the required form") in lpi_proof
  | "true" | "false" -> predefined_proof_generator (List.hd cl) [rule]
  | "" -> raise (SyntaxError "missing rule")
  | _ -> "/* TODO */"

let get_lp_commands = function
| Assume x -> "symbol " ^ x.name ^ " : Prfc (" ^ term_translate x.term ^ ");"   (* ≔ *)
| Step x -> let proof_def =
  match step_translate x.clause x.rule x.annotations with 
  | "/* TODO */" -> "/* TODO */" 
  | lp_proof -> "symbol " ^ x.name ^ " : " ^ lp_proof in 
  proof_def
| _ -> "/* TODO */"

let rec get_lp_script = function
| [] -> ""
| x :: t -> (get_lp_commands x) ^ "\n" ^ get_lp_script t

