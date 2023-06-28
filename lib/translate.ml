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
| Symbol x -> x
| Const c -> let string_of_const = function | Numeral y -> string_of_int y | String y -> y in 
  string_of_const c
| Not t -> "¬ " ^ term_translate t
| Or list -> "(" ^ join_with " ∨ " (map term_translate list) ^ ")"
| And list -> "(" ^ join_with " ∧ " (map term_translate list) ^ ")"
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


let get_lp_commands = function
| Assume x -> "symbol " ^ x.name ^ " ≔ " ^ term_translate x.term ^ ";"
| _ -> "/* TODO */"

let rec get_lp_script = function
| [] -> ""
| x :: t -> (get_lp_commands x) ^ "\n" ^ get_lp_script t

