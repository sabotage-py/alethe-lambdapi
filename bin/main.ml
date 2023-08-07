(* open Cmdliner *)
module P = A2lp.Parse
module T = A2lp.Translate
module Smt2lp = A2lp.Trans_smt2
module S = Smtlib_utils.V_2_6

let fpf = Format.fprintf

type input = 
  | File of string

let process (i : input) : (_,_) result =
  try
    let l = match i with
      | File file ->
        S.parse_file_exn file
    in
    fpf Format.std_formatter "@[<hv>%a@]@." (S.Ast.pp_list Smt2lp.smt2lp_stmt) l;
    Ok ()
  with e ->
    let bt = Printexc.get_backtrace() in
    Error (Printexc.to_string e, bt)

let process_file f = process (File f)

(* let veriT_proof_file =
  let info =
    Arg.info []
      ~doc:"veriT proof trace file" ~docv:"FILE"
  in
  Arg.required (Arg.pos 0 (Arg.some Arg.file) None info) *)

let read_whole_file filename =
  let ch = open_in filename  in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch ; s

let reconstruction file =
  let content = read_whole_file file in 
    let script = P.parse content in
      match script with
      | Ok s -> T.get_lp_script Format.std_formatter s (*Format.printf "%a" pp_proofScript s*)
      | Error e -> fpf Format.std_formatter "%s" e

(* let cmd =
  let doc = "Translate veriT proof into tla_lambdapi" in
  let info = Cmd.info "reconstruction" ~doc in
  Cmd.v info Term.(const reconstruction $ veriT_proof_file)
  
let main () = exit (Cmd.eval cmd)
let () = main () *)

let process_files l =
  (* Printf.printf "process %d files…\n%!" (List.length l); *)
  if List.length l = 2 then
    let f_smt2, f_alethe = List.hd l, List.hd (List.tl l) in 
    let res = match process_file f_smt2 with
    | Ok () -> reconstruction f_alethe
    | Error (_,_) -> () in
    res
  else raise (Invalid_argument "need exactly two files")

let () =
  let l = ref [] in
  Arg.parse (Arg.align []) (fun s -> l := s :: !l) "usage: tip-cat [file]*";
  process_files (List.rev !l)
