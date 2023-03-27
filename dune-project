(lang dune 3.7)

(name reconstruction)

(generate_opam_files true)

(source
 (github NotBad4u/reconstruction))

(authors "Coltellacci Alessio")

(maintainers "Coltellacci Alessio")

(license MIT)

(using menhir 2.1)

(package
 (name reconstruction)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune menhir base ppx_deriving)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
