Translate Alethe proofs to Lambdapi
===================================

This is a program `al2lp` (still underconstruction) to generate a Lambdapi file from the given SMT2 input file and the Alethe file, where the latter is an SMT solver's ouput for the aforementioned SMT2 input file).

[Alethe](https://verit.loria.fr/documentation/alethe-spec.pdf) is a proof format to represent unsatisfiability proofs generated by SMT solvers (in particular veriT).

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assistant
based on the λΠ-calculus modulo rewriting. You may refer to [this paper](https://arxiv.org/pdf/2111.00543.pdf).

Compilation from the source
---------------------------

You can get the source using `git` as follows:
```bash
git clone https://github.com/sabotage-py/alethe-lambdapi
```
Dependencies are described in `al2lp.opam`.

To compile Lambdapi, just run the command `make` in the source directory.

You can run `al2lp` without installing it with `dune exec -- al2lp [smt2 file] [alethe file]`.


Source files
------------

The decision to write this program on top of the [Alethe parser](https://github.com/NotBad4U/reconstruction) was made due to the unavailability of the said parser on `opam`.

The following files remain unchanged from https://github.com/NotBad4U/reconstruction and are required for parsing the Alethe files. The copyright for these belong with the original author.
- `lib/ast.ml`: type definitions required for parsing the alethe file.
- `lib/lexer.mll`
- `lib/parse.ml`
- `parser.mly`




Thanks
------

written by Nabin Sahoo in 2023.
