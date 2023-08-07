type l_term = string

let join_with s list =
  let rec aux str = function
    | [] -> str
    | x :: t -> ( match str with "" -> aux x t | _ -> aux (str ^ s ^ x) t)
  in
  aux "" list

(* returns the index of el in list *)
let rec find_idx el = function
  | [] -> raise Not_found
  | x :: t -> if x = el then 0 else 1 + find_idx el t

let rec find_idx_opt el = function
  | [] -> None
  | x :: t -> (
      if x = el then Some 0
      else match find_idx_opt el t with None -> None | Some i -> Some (1 + i))

let unique_list list =
  let rec aux keeper = function
    | [] -> keeper
    | x :: t -> (
        match find_idx_opt x keeper with
        | None -> aux (x :: keeper) t
        | _ -> aux keeper t)
  in
  List.rev (aux [] list)

let elim_last list =
  let rec aux keeper = function
    | [] | [ _ ] -> keeper
    | x :: t -> aux (x :: keeper) t
  in
  List.rev (aux [] list)

let rec rem_el el = function
  | [] -> []
  | x :: t -> if x = el then t else x :: rem_el el t

let rec get_indices (alist : 'a list) (blist : 'a list) : int option list =
  (*returns the list of indices in blist of the elements of alist*)
  match alist with
  | x :: t -> find_idx_opt x blist :: get_indices t blist
  | [] -> []

(* let find_idx el list = List.find
   (function | -1 -> false | _ -> true)
   (
     List.mapi (fun i r -> if r = el then i else -1) list
   ) *)

(* let rec get_str_n str = function
   | 0 -> ""
   | n -> str ^ get_str_n str (n - 1) *)

(* let map f a =
     let rec aux b = function
     | [] -> b
     | x :: t -> aux ((f x) :: b) t
   in aux [] (List.rev a);; *)

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
