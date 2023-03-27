{
    open Lexing
    open Parser

    exception SyntaxError of string

    let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
        { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1
        }
}

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

(* Helper regexes *)
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']

let int = '-'? digit+
let float=('0' | ['1'-'9'] digit*) '.' digit+

(*
    A non-empty sequence of letters, digits and the characters
    + - / * = % ? ! . $ _  &  < > @ that does not start with a digit
*)
let simpl_symbol = (alpha | ['+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']) (alpha|digit| ['+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@'])*

(* 
    A simpl_symbol or a sequence of whitespace and printable characters that
    starts and ends with | and does not otherwise include | or \
    TODO: add the regex tokens to matches any character except | and \ (Should be something like /[^abc]+/g)
*)
 let symbol = simpl_symbol | '|' (alpha|digit|['_']) (alpha|whitespace|digit|['_'])* '|'

rule read_token = parse
| "//" { read_single_line_comment lexbuf } (* We add the support of comments to help debuging *)
| "/*" { read_multi_line_comment lexbuf } 
| "cl"
    { CLAUSE }
| "forall"
    { FORALL }
| "exists"
    { EXISTS }
| "and"
    { AND }
| "or"
    { OR }
| "not"
    { NOT }
| "choice"
    { CHOICE }
| ":="
    { ASSIGN }
| "="
    { EQUAL }
| ":rule"
    { RULE }
| ":premises"
    { PREMISES }
| "assume"
    { ASSUME }
| "step" | ":step"
    { STEP }
| ":args"
    { ARGS }
| "anchor"
    { ANCHOR }
| ":discharge"
    { DISCHARGE }
| int as i
    { INT (int_of_string i) }
| symbol { SYMBOL (Lexing.lexeme lexbuf) }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| eof
    { EOF }
| whitespace { read_token lexbuf }
| newline { next_line lexbuf; read_token lexbuf }
| _
    { raise (SyntaxError (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

and read_single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf } 
  | eof { EOF }
  | _ { read_single_line_comment lexbuf } 
  
and read_multi_line_comment = parse
  | "*/" { read_token lexbuf } 
  | newline { next_line lexbuf; read_multi_line_comment lexbuf } 
  | eof { raise (SyntaxError ("Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf } 
  