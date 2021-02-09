(assert (and (boundp '+nn+) (constantp '+nn+)) ()
  "~&Don't forget to set +nn+ to the level, as with~&  (defconstant +nn+ 12)")

(assert (and (boundp '+make-sp+) (constantp '+make-sp+)) ()
  "~&Don't forget to set +make-sp+ to the sparse-elt~&constructor for your ring.  Examples:~&[i]  (defconstant +make-sp+ #'make-sp-z)~&[ii] (def-sp-p 31991)~&     (defconstant +make-sp+ #'make-sp-31991)")

(labels ((compile-and-load (file)
           (compile-file file)
           (load file)))
  (compile-and-load "p3")
  (compile-and-load "cardp3")
  (compile-and-load "eqco4N"))
