open Cmdliner
open Reconstruction.Parse
(* open Reconstruction.Ast *)
open Reconstruction.Translate

let veriT_proof_file =
  let info =
    Arg.info []
      ~doc:"veriT proof trace file" ~docv:"FILE"
  in
  Arg.required (Arg.pos 0 (Arg.some Arg.file) None info)

let read_whole_file filename =
  let ch = open_in filename  in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch ; s

let reconstruction file =
  let content = read_whole_file file in 
    let script = parse content in
      match script with
      | Ok s -> print_string (get_lp_script s) (*Format.printf "%a" pp_proofScript s*)
      | Error e -> print_string e

let cmd =
  let doc = "Translate veriT proof into tla_lambdapi" in
  let info = Cmd.info "reconstruction" ~doc in
  Cmd.v info Term.(const reconstruction $ veriT_proof_file)
  
let main () = exit (Cmd.eval cmd)
let () = main ()