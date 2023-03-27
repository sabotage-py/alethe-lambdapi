%{
  open Ast
%}

%token <int> INT
%token <string> SYMBOL
%token LPAREN RPAREN

%token AND
%token OR
%token EQUAL
%token NOT
%token FORALL
%token EXISTS
%token ASSIGN
%token CHOICE

%token CLAUSE
%token STEP
%token PREMISES
%token ASSUME
%token RULE
%token ANCHOR
%token ARGS
%token DISCHARGE

%token EOF

%start <Ast.proofScript> proof

%%
 
/* 
  ⟨ proof ⟩ ::=  ⟨ proof_command ⟩*
*/
proof:
| command = proof_command EOF { [command] }
| command = proof_command p = proof { command :: p}

/*
  Lexer transform the SMT-lib proof rule 'or', 'and' into OR, AND.
  We need to cast them back to string to instantiate a variant :rule ⟨ symbol ⟩ in proof_command.
*/
rule:
| OR { "or" }
| AND { "and" }
| s=SYMBOL { s }

/*
  ⟨ proof_command ⟩ ::= (assume ⟨ symbol ⟩ ⟨ proof_term ⟩ )
  | (step ⟨ symbol ⟩ ⟨ clause ⟩ :rule ⟨ symbol ⟩ ⟨ step_annotation ⟩ )
  | (anchor :step ⟨ symbol ⟩ )
  | (anchor :step ⟨ symbol ⟩ :args ⟨ proof_args ⟩ )
  | (define-fun ⟨ function_def ⟩ 
*/
proof_command:
| LPAREN ASSUME name=SYMBOL term=proof_term RPAREN { Assume { name; term }  } // Assume step
| LPAREN STEP name=SYMBOL clause=clause RULE rule=rule annotations=option(step_annotation) RPAREN { Step { name; clause; rule; annotations }  }
| LPAREN ANCHOR STEP name=SYMBOL RPAREN { Anchor { name; args=[] } }
| LPAREN ANCHOR STEP name=SYMBOL ARGS args=proof_args  RPAREN { Anchor { name; args } }

/*
  ⟨ clause ⟩ ::= (cl ⟨ proof_term ⟩* )
*/
clause:
| LPAREN CLAUSE terms=list(proof_term) RPAREN { terms }

/*
⟨ proof_args ⟩ ::= ( ⟨ proof_args ⟩+ )
*/
proof_args: LPAREN args=nonempty_list(proof_arg) RPAREN { args }

/*
  ⟨ proof_arg ⟩ ::= ⟨ symbol ⟩
  | ( ⟨ symbol ⟩  ⟨ proof_term ⟩ )
*/
proof_arg:
| LPAREN ASSIGN term_l=proof_term term_r=proof_term RPAREN { Assign( term_l, term_r  ) }
| digit=INT { Numeric (digit) }
| LPAREN digit=INT RPAREN { Numeric (digit) }
| symbol=SYMBOL { Name(symbol) }


/*
  ⟨ step_annotation ⟩ ::= :premises ( ⟨ symbol ⟩+ )
  | :args ⟨ proof_args ⟩
  | :premises ( ⟨ symbol ⟩+ ) :args ⟨ proof_args ⟩
  | :discharge ( ⟨ symbol ⟩+ )
  
  NOTE: Currently this :discharge pattern is not referenced in the Aleth documentation.
*/
step_annotation:
| PREMISES LPAREN premises=nonempty_list(SYMBOL) RPAREN { Annotation (premises, []) }
| ARGS args=proof_args { Annotation ([], args) }
| PREMISES LPAREN premises=nonempty_list(SYMBOL) RPAREN  ARGS args=proof_args { Annotation (premises, args) }
| DISCHARGE LPAREN premises=nonempty_list(SYMBOL) RPAREN { Discharge (premises) }

/* 
   ⟨ term ⟩ ::=  ⟨ spec_constant ⟩
  |  ⟨ qual_identifer ⟩
  | (  ⟨ qual_identifer ⟩  ⟨ term ⟩+ )
  | ( let (  ⟨ var_binding ⟩+ )  ⟨ term ⟩ )
  | ( forall (  ⟨ sorted_var ⟩+ )  ⟨ term ⟩ )
  | ( exists (  ⟨ sorted_var ⟩+ )  ⟨ term ⟩ )
  | ( match ⟨   ⟨ term ⟩ (  ⟨ match_case ⟩+ ) )
  | ( !  ⟨ term ⟩  ⟨ attribute ⟩+ )
  | (choice ( ⟨ sorted_var ⟩+ ) ⟨ proof_term ⟩ ) -- proof_term is ⟨ term ⟩ from SMT_LIB extended with choice
*/
proof_term:
| const=spec_constant { Const(const) }
| LPAREN FORALL LPAREN sorted_vars=nonempty_list(sorted_var) RPAREN term=proof_term RPAREN { Forall (sorted_vars, term)  }
| LPAREN EXISTS LPAREN sorted_vars=nonempty_list(sorted_var) RPAREN term=proof_term RPAREN { Exists (sorted_vars, term)  }
| LPAREN NOT t=proof_term RPAREN  { Not(t) }
| LPAREN AND ts=nonempty_list(proof_term) RPAREN  { And(ts) }
| LPAREN OR ts=nonempty_list(proof_term) RPAREN  { Or(ts) }
| LPAREN EQUAL l=proof_term r=proof_term RPAREN  { Equal(l,r) }
| LPAREN identifier=qual_identifier terms=nonempty_list(proof_term) RPAREN { Application(identifier, terms) }
| identifier=qual_identifier { Symbol(identifier) }
| LPAREN CHOICE LPAREN sorted_vars=nonempty_list(sorted_var) RPAREN term=proof_term RPAREN { Choice (sorted_vars, term) }

/*
  ⟨ qual_identifer ⟩ ::= ⟨ identifer ⟩ | ( as ⟨ identifer ⟩ ⟨ sort ⟩ )
  NOTE we treat ⟨ identifer ⟩ as only a symbol for now
*/
qual_identifier:
| s=SYMBOL { s }

/*
  ⟨ spec_constant ⟩ ::=  ⟨ numeral ⟩ |  ⟨ decimal ⟩ | ⟨ hexadecimal ⟩ | ⟨ binary ⟩ | ⟨ string ⟩
*/
spec_constant: 
| n=INT { Numeral(n) }

/*
  ⟨ sort ⟩ ::= ⟨ identifer ⟩
  | (  identifer ⟩ ⟨ sort ⟩+ )
*/
sort:
| identifier=SYMBOL { Sort(identifier) }
| LPAREN identifier=SYMBOL sort=nonempty_list(sort) RPAREN { SortParametrized(identifier, sort) }


(*
  ⟨ sorted_var ⟩ ::= ( ⟨ symbol ⟩ ⟨ sort ⟩ )
*)
sorted_var: LPAREN identifier=SYMBOL sort=sort RPAREN { SortParametrized(identifier, [sort])  }