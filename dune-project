(lang dune 3.6)

(name alg_w)

(generate_opam_files true)

(source
 (github junewunder/alg_w))

(authors "june wunder")

(maintainers "june wunder")

(license MIT)

(documentation https://url/to/documentation)

(package
 (name alg_w)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  ppx_deriving)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
