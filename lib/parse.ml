open Base
open Lexing

(* Prints the line number and character number where the error occurred.*)
let print_error_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


let parse input =
  let filebuf = Lexing.from_string input in
    try
      Ok (Parser.proof Lexer.read_token filebuf)
    with
      | Lexer.SyntaxError msg ->
          Error msg
      | Parser.Error ->
        let error_msg = Printf.sprintf "%s: syntax error@." (print_error_position filebuf) in
          Error error_msg