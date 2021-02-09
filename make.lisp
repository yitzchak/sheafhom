(in-package cl-user)

(defpackage "SHEAFHOM2"
  (:nicknames "SHH2")
  (:use "COMMON-LISP")
  (:export
   ;; from macros.lisp.  Export all except with-gensyms, which
   ;; conflicts with clisps's with-gensyms.
   "AAND" "AIF" "AWHEN" "AWHILE" "DOTIMES-F" "IT" "NNFIXNUM" "PUTHASH"
   "SPLICER-DELETE" "SPLICER-ENDP" "SPLICER-FWD" "SPLICER-INSERT"
   "SPLICER-MODIFY" "SPLICER-NCONC" "SPLICER-READ" "SPLICER-SPLIT"
   "SPLICER-TAIL" "TILL" "WITH-SPLICER"
   ;; from vendor-specific.lisp
   "SHOW-LINE-GRAPH"
   ;; from multi-file.lisp
   "MULTI-FILE" "MAKE-MULTI-FILE" "*MULTI-FILE-COMPRESSOR*"
   "*MULTI-FILE-COMPRESSED-NAMER*" "*MULTI-FILE-DECOMPRESSOR*"
   "MULTI-FILE-PRINT" "MULTI-FILE-LOCK"
   "MULTI-FILE-INIT-READ" "MULTI-FILE-READ" "MULTI-FILE-PEEK"
   "MULTI-FILE-DELETE"
   ;; from category.lisp
   "CAT-OBJ" "CAT-MFM"
   "MAKE-ID-MFM"
   "CAT-EQUALP" "COMPOSE" "ID-MFM-P" "MONIC-P" "EPIC-P"
   "ISOMORPHISM-P" "MAKE-INVERSE-MFM"
   ;; from mset.lisp
   "MSET" "MSET-MEMBER" "MSET-SIZE" "MSET-ITERATOR" "DO-MSET"
   "LAZY-SET" "HASH-SET" "EQUALP-KEY" "MAKE-HASH-SET" "IOTA" "MAKE-EMPTY-SET"
   "MSET-EMPTYP" "MSET-EQUAL" "MSET-SUBSET" "MSET-DISJOINT-UNION"
   "MSET-INTERSECTION" "MSET-DIFFERENCE" "MSET-UNION" "MSET-EXCLUSIVE-OR"
   "MSET-PRODUCT-ITERATOR" "MSET-COUNT-IF" "MSET-GET-ONE-ELT"
   "MSET-FIND-IF" "MSET-SUBSETP"
   "MSET-SOME" "MSET-EVERY" "MSET-NOTANY" "MSET-NOTEVERY"
   ;; from strongly-conn.lisp
   "STRONGLY-CONN-VERTICES" "STRONGLY-CONN-NUM-VERTICES"
   "STRONGLY-CONN-EDGES-FROM" "STRONGLY-CONN-ENDING-VERTEX"
   "STRONGLY-CONN-SCC" "INPUT-STRONGLY-CONN-GRAPH"
   ;; from numthy.lisp
   "*PRIMES*" "PRIMEP" "VALUATION" "FACTOR" "IS-POWER-OF"
   "TOTIENT" "EXT-GCD" "INV-MOD" "POWER-MOD" "PRIMITIVE-ROOT"
   "QUAD-RESIDUE"
   ;; from matrix.lisp
   "M-NUM-ROWS" "M-NUM-COLS" "M-ZEROP" "M-ID-P" "M-ADD" "M-SUBTRACT"
   "M-NEGATE" "M-PRODUCT-ZEROP" "M-MULT" "M-TRANSPOSE" "M-INVERSE"
   "M-INVERSE-TRANSPOSE" "M-TRANSLATE" "M-KER" "MAT"
   ;; from dense-matrix-z.lisp
   "DENSE-MATRIX-Z" "MAKE-DENSE-MATRIX-Z" "DO-LLL"
   ;; from dense-matrix-mod-p.lisp
   "DENSE-MATRIX-MOD-P" "MAKE-DENSE-MATRIX-MOD-P"
   "MAKE-DENSE-MATRIX-MOD-P-ZERO" "ROW-REDUCE-MOD-P" 
   ;; from sparse-elt.lisp
   "SP-EMBED-Z" "COPY-SP" "SP-PRINT-VALUE" "SP-I-FUNC" "SP-I"
   "SP-NEG-ONE-P" "SP-ONEP" "SP-ZEROP" "SP-UNITP" "SP-ADD" "SP-SUBTRACT"
   "SP-MULT" "SP-DIVIDES" "SP-PRETTY-ASSOCIATE" "SP-=" "SP-NEGATE"
   "SP-EUC-NORM" "SP-NEG-CLOSEST-QUOTIENT" "SP-DIVIDED-BY" "SP-ROUNDED-REM"
   "MAKE-SP-Z" "DEF-SP-P" "SP-RING-NAME" "SP-Z-P" "SP-FIELD-P" "SP-F_P-P"
   ;; from sparse-v.lisp
   "SPARSE-V" "INPUT-SPARSE-V"
   "V-ADD" "V-ADD-NONDESTR" "V-SUBTRACT" "V-SUBTRACT-NONDESTR"
   "V-SCALAR-MULT" "V-SCALAR-MULT-F" "V-NEGATE" "V-NEGATE-F"
   "V-NEGATE-NONDESTR" "V-ALTER"
   "V-ALTER-F" "V-ALTER-ELT" "V-ALTER-ELT-F" "V-NEGATE-ELT"
   "V-NEGATE-ELT-F" "V-SWAP" "V-SWAP-F" "V-DOT" "V-GET" "V-SET"
   "V-SET-F" "V-ZEROP" "V-SINGLETON-P"
   ;; from elem-matrix.lisp
   "PERM2" "PERM" "TRANSV"
   ;; from csparse.lisp
   "CSPARSE" "MAKE-CSPARSE-ZERO"
   "INPUT-CSPARSE" "CSPARSE-COPY" "PRINT-ENTRIES"
   "ALTER-COL" "ALTER-ROW" "SWAP-COLS" "SWAP-ROWS" "NEGATE-COL"
   "NEGATE-ROW" "SPARSITY" "MAKE-ZERO-AND-ID" "M-ADD"
   "M-SUBTRACT" "M-NEGATE" "CSPARSE-GET"
   "DO-ROWS-CSPARSE" "M-PRODUCT-ZEROP"
   "CSPARSE-SET" "M-ZEROP" "M-ID-P" "CSPARSE-CONCAT-LEFT-RIGHT"
   "CSPARSE-MOVE-FROM-DENSE" "CSPARSE-MOVE-TO-DENSE" "HIT-WITH-LLL"
   "TIME-STAMP" "*VERBOSE*" "*SHOW-STATS*" "*SHOW-CSW*"
   "*ALLOW-MARKOWITZ*" "*ALLOW-BLOCK-TRI*" "*BLOCK-TRI-REP-CT*"
   "*ALLOW-LLL*" "*LLL-WIDTH*" "*LLL-THRESHOLD*" "*LLL-NEXT-TRY*"
   "*ALLOW-MINOR-TRICK*" "*MINOR-TRICK-THRESHOLD*" "*MINOR-TRICK-COL-FUNC*"
   "*ALLOW-WIEDEMANN-WINNOW*" "*WIEDEMANN-WINNOW-THRESHOLD*"
   "*ALLOW-DISK-HNF*" "*DISK-HNF-THRESHOLD*"
   "*DISK-HNF-WIDTH*" "*DISK-HNF-BATCH-SIZE*"
   "*ALLOW-MODULAR-HNF*" "*MODULAR-HNF-THRESHOLD*"
   "SNF" "MAKE-SNF" "MAKE-SNF-FROM-DISK"
   "DO-SNF-P" "DO-SNF-P-REV" "DO-SNF-Q" "DO-SNF-Q-REV"
   "RANK" "NUM-UNITS" "TORSION" "M-IMAGE-CONTAINED-IN-IMAGE"
   "SNF-DIAGONAL-P" "PIVOT-METHOD" "V-NORM-SQ"
   "HNF" "HNF-F" "M-INVERSE-IMAGE"
   "PERM-ECH" "MAKE-PERM-ECH-FROM-CSPARSE" "MAKE-PERM-ECH-FROM-DISK"
   "DO-PERM-ECH-COLS"
   "BERLEKAMP-MASSEY" "WIEDEMANN-SQUARE-DEPENDENCY" "WIEDEMANN-WINNOW"
   ;; from group-elt.lisp
   "GROUP-ELT" "MULT-TWO" "INVERSE" "IDENTITY-ELT" "IDENTITYP"
   "MULT" "GROUP-ELT-EQUAL" "COMMUTES-WITH" "CONJ-Y-X-YINV"
   "CONJ-YINV-X-Y" "POWER" "COMMUTING-GROUP-ELT"
   "MOD-1" "MAKE-MOD-1" "FACTOR1" "FACTOR2" "SEMIDIRECT-PRODUCT-ELT"
   "MAKE-SEMIDIRECT-PRODUCT-ELT" "DIRECT-PRODUCT-ELT"
   "MAKE-DIRECT-PRODUCT-ELT"
   ;; from group.lisp
   "GROUP" "CONJ-CLASS" "CONJ-CLASS-NUM" "CONJ-CLASS-INDEX" "GP-CHAR"
   "DO-CONJ-CLASS" "DO-CONJ-CLASS-REP" "CONJ-CLASS-REP" "GP-CHAR-VALUE"
   "GROUP-STD-CONJ-CHAR" "MAKE-GROUP" "SUBGROUP"
   "TRIVIAL-SUBGROUP" "ORDER" "ABELIANP" "CENTRALIZER" "CENTER"
   "COMMUTATOR-SUBGROUP" "SYLOW" "SIMPLEP" "GENERATORS" "EXPONENT"
   "LEFT-COSET-REPS"
   ;; (skipping class-function and gp-char items for now)
   "CYCLIC-GROUP" "MAKE-CYCLIC-GROUP" "ABELIAN-GROUP"
   "MAKE-ABELIAN-GROUP" "P-GROUP" "MAKE-P-GROUP" "SEMIDIRECT-PRODUCT"
   "MAKE-SEMIDIRECT-PRODUCT" "DIRECT-PRODUCT" "MAKE-DIRECT-PRODUCT"
   "DIHEDRAL-GROUP" "MAKE-DIHEDRAL-GROUP"   
   ;; from homolalg.lisp
   ;; -- additive categories
   "ADD-CAT-OBJ" "ADD-CAT-MFM" "DIRECT-SUM"
   "MAKE-ZERO-OBJ" "MAKE-ZERO-MFM"
   "MFM-FROM-DIRECT-SUM" "MFM-TO-DIRECT-SUM"
   "ADD-CAT-ZEROP" "ADD" "SUBTRACT" "COMPOSITION-ZEROP"
   ;; -- abelian categories
   "ABELIAN-CAT-OBJ" "ABELIAN-CAT-MFM"
   "KER" "PULLBACK-TO-KER"
   "COKER" "PULLBACK-TO-COKER"
   ;; -- free Z-modules
   "FREE-Z-MODULE" "FREE-Z-MFM" "FREE-Z-DIRECT-SUM"
   "CSPARSEZ-MFM" "FREE-Z-ZERO-MFM"
   "MAKE-FREE-Z-MODULE" "MAKE-FREE-Z-MFM" "MAKE-FREE-Z-MODULE-DIRECT-SUM"
   "ALLOW-SOU-COORD-CHANGES" "ALLOW-TAR-COORD-CHANGES" "DESTROY-MATRIX"
   ;; -- finitely-generated Z-modules
   "Z-MODULE" "Z-MFM" "Z-MODULE-DIRECT-SUM"
   ;; -- cochain complexes
   "CCX" "CCX-MAP"
   "MAKE-CCX"
   "CCX-TERM" "CCX-DIFF" "CCX-MAX-DEG" "CCX-MIN-DEG" "CCX-MAP-TERM"
   ;; -- tensors
   "TENSOR-OBJ" "TENSOR-FREE-Z-MODULE"
   "MAKE-TENSOR-FREE-Z-MODULE"
   "MAKE-TENSOR-MORPHISM"
   ;; skip two-complex.lisp; it's only for testing
   ))

(use-package "SHH2")

(labels ((compile-and-load (file)
           (compile-file file)
           (load file)))
  (compile-and-load "macros")
  (compile-and-load "vendor-specific")
  (compile-and-load "multi-file")
  (compile-and-load "category")
  (compile-and-load "mset")
  (compile-and-load "strongly-conn")
  (compile-and-load "numthy")
  (compile-and-load "matrix")
  (compile-and-load "dense-matrix-z")
  (compile-and-load "dense-matrix-mod-p")
  (compile-and-load "sparse-elt")
  ;;(compile-and-load "sparse-elt-p")
  ;;(compile-and-load "sparse-elt-12379x")
  (compile-and-load "sparse-v")
  (compile-and-load "elem-matrix")
  (compile-and-load "csparse")
  (compile-and-load "group-elt")
  ;;(compile-and-load "group")
  (compile-and-load "homolalg")
  (compile-and-load "two-complex")
  ;;(compile-and-load "groupcoh")
  )

(in-package cl-user)
