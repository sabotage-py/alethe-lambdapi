type sort =
| Sort of string
| SortParametrized of string * sort list
and sorts = sort list
[@@deriving show]

type constant =
| Numeral of int
| String of string
[@@deriving show]


type term =
| Symbol of string
| Const of constant
| Not of term
| And of terms
| Or of terms
| Equal of term * term
| Application of string * terms
| Forall of sorts * term
| Exists of sorts * term
| Choice of sorts * term
and terms = term list
[@@deriving show]

type premises = string list
[@@deriving show]

type arg =  
| Name of string
| Numeric of int
| Assign of term * term
[@@deriving show]

type args = arg list
[@@deriving show]

type step_annotation = 
| Annotation of premises * args
| Discharge of premises
[@@deriving show]

type proof_command = 
| Assume of { name: string; term: term  }
| Step of { name: string; clause: terms; rule: string; annotations: step_annotation option }
| Anchor of { name: string; args: args  }
[@@deriving show]

type proofScript = proof_command list
[@@deriving show]
