(in-package shh2)

(declaim (optimize speed))

;;; A sparse-elt is an entry in a sparse matrix defined over an
;;; integral domain D.  Specifically, a sparse-elt is an element of a
;;; sparse vector (see sparse-v), and a sparse matrix is a sequence of
;;; sparse-v objects giving its columns (see csparse).  Each
;;; sparse-elt is a data structure holding two values, an index in a
;;; sparse-v and a value in D.  Different matrices can use different D
;;; in the same runtime session.

;;; An object-oriented design decision in Sheafhom 2.x is that the
;;; arithmetic of D is controlled by the sparse-elts, not by the
;;; matrix data structure or global program settings.  One implements
;;; a given D by implementing several generic functions, the ones
;;; listed with "defgeneric" in the file sparse-elt.lisp.  These
;;; functions perform basic operations on sparse-elts like addition
;;; and multiplication.  Sparse-elts are not organized into a
;;; hierarchy of classes, but that's not necessary, because the
;;; generic functions handle them in a polymorphic way.

;;; Here are some requirements for all sparse-elt implementations.
;;; The index must be non-negative, or negative to mean 'unspecified'.
;;; It must be a fixnum, i.e., a single-precision integer.  (Sheafhom
;;; defines the type nnfixnum of non-negative fixnums.)  A sparse-elt
;;; should be immutable: if a change is needed, don't modify its
;;; contents, but create a new sparse-elt instead.  The value may be
;;; zero, but it is an error if a sparse-elt with value zero becomes
;;; an element of a sparse-v.  nil must not be a sparse-elt.  Finally,
;;; equalp must test whether two sparse-elts have the same index and
;;; the same value.  This ensures that equalp will also test whether
;;; sparse-v's and csparse's are mathematically equal.  The
;;; requirement on equalp means sparse-elts cannot be implemented as
;;; classes, but must be structures or other built-in types.

;;; A fundamental case is D = Z, the ring of rational integers.  The
;;; file sparse-elt.lisp, which is loaded by default, implements a
;;; sparse-elt over Z as an ordered pair (a "cons") such as (i . v)
;;; with index i and value v an arbitrary-precision integer.  This
;;; uses memory efficiently.  In Allegro Common Lisp, for example,
;;; when v happens to be small enough for single-precision, the entire
;;; sparse-elt fits in 8 bytes, 4 for i and 4 for v.

;;; For other D, a sparse-elt will likely be a custom-written
;;; structure.  As another fundamental example, sparse-elt.lisp has an
;;; implementation def-sp-p for finite fields D of prime order.

;;; Some applications use a single finite field D of prime order and
;;; do not use Z.  Here the finite field should get the efficient cons
;;; representation.  The file sparse-elt-p.lisp is a sample
;;; implementation hard-coded for the field of order 12379.  If you
;;; wish to use it, load sparse-elt-p.lisp instead of sparse-elt.lisp,
;;; not both.

;;; Each type of sparse-elt should have a constructor function,
;;; typically named make-sp-[...].  It should take two arguments,
;;; index and value.  The index will be a fixnum.  The constructor
;;; should accept values that are integers, to realize the canonical
;;; map Z -> D, and should also accept any values needed for more
;;; specialized D.  Parts of the code take an argument make-sp
;;; pointing to such a constructor and defaulting to make-sp-z.

;;; When binary operations like sp-add take an optional argument
;;; new-index, the index of the result is new-index if it is present.
;;; Otherwise, it is always the index of the first sparse-elt
;;; argument.

;;; -------------------- The public interface  --------------------

(defgeneric copy-sp (elt new-index)
  (:documentation
   "Returns a new sparse-elt with elt's value and index new-index.
If elt's index equals new-index, returns elt itself (as sparse-elts
are immutable)."))

(defgeneric sp-embed-z (sample-elt z-value &optional new-index)
  (:documentation
   "Constructs and returns a sparse-elt of the same type as sample-elt,
with value the image of the integer z-value under the canonical
map Z -> D.  The index is new-index if present, else that of
sample-elt."))

(defgeneric sp-i-func (elt)
  (:documentation
   "The index of a sparse-elt in a sparse vector (see sparse-v).  It
must be non-negative, or negative to mean 'unspecified'.  It must be
a fixnum (a single-precision integer).
  The preferred way to access the index is (sp-i elt)."))

(defmacro sp-i (elt)
  "A wrapper around sp-i-func that declares the result is a fixnum."
  `(the fixnum (sp-i-func ,elt)))

(defgeneric sp-= (x y)
  (:documentation
   "True iff the values are equal in the domain D.  Note: as we've
required, equalp tests for equality of index and value simultaneously."))

(defgeneric sp-print-value (elt &optional stream)
  (:documentation "Prints the value of the sparse-elt to the stream.
Does not print the index.  The stream defaults to nil, meaning
the value is returned as a string."))

(defgeneric sp-ring-name (elt)
  (:documentation
   "Returns a string that is a short name for the ring underlying
this sparse-elt."))

;;; Operations over any commutative ring with identity.

(defgeneric sp-zerop (elt)
  (:documentation "True iff the sparse-elt has value 0."))

(defgeneric sp-onep (elt)
  (:documentation "True iff the sparse-elt has value 1."))

(defgeneric sp-neg-one-p (elt)
  (:documentation "True iff the sparse-elt has value -1."))

(defgeneric sp-unitp (elt)
  (:documentation "True iff the sparse-elt's value is a unit in D."))

(defgeneric sp-add (x y &optional new-index)
  (:documentation
   "Sum of two sparse-elts.  Index is new-index if present,
else that of x."))

(defgeneric sp-subtract (x y &optional new-index)
  (:documentation
   "Difference of two sparse-elts.  Index is new-index if present,
else that of x."))

(defgeneric sp-negate (elt &optional new-index)
  (:documentation
   "Additive inverse of a sparse-elt.  Index is new-index if present,
else that of elt."))

(defgeneric sp-mult (x y &optional new-index)
  (:documentation
   "Product of two sparse-elts.  Index is new-index if present,
else that of x."))

(defgeneric sp-divides (divisor dividend)
  (:documentation
   "True iff divisor | dividend.  That is, tests whether there exists
q in D such that q * divisor = dividend.  It is an error if the
divisor has zero value (see sp-zerop)."))

(defgeneric sp-divided-by (x y &optional new-index)
  (:documentation
   "Returns x/y exactly.  It is an error if y's value is zero or if
the division has a non-zero remainder (see sp-zerop and sp-divides).
Index is new-index if present, else that of x."))

(defgeneric sp-pretty-associate (elt)
  (:documentation
   "Returns two sparse-elts x and y.  There is a unit u in D such that
x * u = elt, and such that humans consider the value of x prettier
than that of elt.  (Example over Z: x is the absolute value of elt.)
u is the value of y.  The index of x and y is that of elt."))

;;; Operations over Euclidean domains.

(defgeneric sp-euc-norm (elt)
  (:documentation
  "Returns the Euclidean norm of the value of elt, as an integer.
If the domain D is not Euclidean, calling this method is an error."))

(defgeneric sp-neg-closest-quotient (x y &optional new-index)
  (:documentation
  "Returns a sparse-elt q such that q * y + x has value as small as
possible for sp-euc-norm.  In other words, returns -x/y rounded to the
nearest element of D.  If the domain D is not Euclidean, or if y's
value is zero, calling this method is an error.  The index of q is
new-index if present, else that of x."))

(defgeneric sp-rounded-rem (x y &optional new-index)
  (:documentation
  "Returns a sparse-elt of value q * y + x, where q is as in
sp-neg-closest-quotient.  In other words, returns the remainder
corresponding to q.  If the domain D is not Euclidean, or if y's value
is zero, calling this method is an error.  The index is new-index if
present, else that of x."))

(defgeneric sp-integrity-check (elt &key message)
  (:documentation
   "Signals an error if the sparse-elt elt has internal errors.  To
provide an (optional) error message, use (... :message the-message)."))

;;; For Z.

(defgeneric sp-z-p (elt)
  (:documentation "True iff the underlying domain is Z."))

(defgeneric sp-integer-value (elt)
  (:documentation
   "If the underlying domain is Z, return the value of elt as an
integer.  Otherwise, signal an error."))

(defgeneric sp-integer-lift (elt)
  (:documentation
   "If D is a quotient of Z, returns a lift to Z of elt's value."))

;;; For fields.

(defgeneric sp-field-p (elt)
  (:documentation "True iff the underlying domain is a field."))

(defgeneric sp-f_p-p (elt)
  (:documentation
   "True iff the underlying domain is the field F_p of prime order.
Returns p if it is, and nil if not."))

;;; ---------- General implementations ----------

(defmethod copy-sp :around (x new-index)
  "If new-index is not provided, or if the new and old indices are equal,
return x without copying."
  (if (or (null new-index) (= (sp-i x) (the fixnum new-index)))
      x
    (call-next-method)))

(defmethod sp-integrity-check ((elt t) &key message)
  "Default method indicating there is no error."
  (declare (ignore message))
  nil)

(defmethod sp-z-p ((elt t))
  "Default method: says elt is not over Z."
  nil)

(defmethod sp-integer-value ((elt t))
  "Default method: signals an error saying elt is not over Z."
  (error "This sparse-elt's value is not an integer: ~A" elt))

(defmethod sp-field-p ((elt t))
  "Default method: says elt is not over a field."
  nil)

(defmethod sp-f_p-p ((elt t))
  "Default method: says elt is not over a field of p elements."
  nil)

;;; ---------- Implementation for D = Z via conses ----------

(defmethod make-sp-z ((index integer) (value integer))
  "Creates a sparse-elt over Z, the ring of rational integers."
  (cons index value))

(defmethod copy-sp ((x cons) new-index)
  (cons new-index (cdr x)))

(defmethod sp-print-value ((elt cons) &optional stream)
  (format stream "~D" (the integer (cdr elt))))

(defmethod sp-i-func ((elt cons))
  (car elt))

(defmethod sp-= ((x cons) (y cons))
  (= (the integer (cdr x)) (the integer (cdr y))))

(defmethod sp-embed-z ((sample-elt cons) (value integer) &optional new-index)
  (cons (or new-index (car sample-elt)) value))

(defmethod sp-ring-name ((elt cons))
  "Z")

(defmethod sp-zerop ((elt cons))
  (zerop (the integer (cdr elt))))

(defmethod sp-onep ((elt cons))
  (= 1 (the integer (cdr elt))))

(defmethod sp-neg-one-p ((elt cons))
  (= -1 (the integer (cdr elt))))

(defmethod sp-unitp ((elt cons))
  (let ((v (cdr elt)))
    (declare (integer v))
    (or (= v 1) (= v -1))))

(defmethod sp-add ((x cons) (y cons) &optional new-index)
  (cons (or new-index (car x))
	(+ (the integer (cdr x)) (the integer (cdr y)))))

(defmethod sp-subtract ((x cons) (y cons) &optional new-index)
  (cons (or new-index (car x))
	(- (the integer (cdr x)) (the integer (cdr y)))))

(defmethod sp-negate ((elt cons) &optional new-index)
  (cons (or new-index (car elt))
	(- (the integer (cdr elt)))))

(defmethod sp-mult ((x cons) (y cons) &optional new-index)
  (cons (or new-index (car x))
	(* (the integer (cdr x)) (the integer (cdr y)))))

(defmethod sp-divides ((x cons) (y cons))
  (zerop (the integer (rem (the integer (cdr y)) (the integer (cdr x))))))

(defmethod sp-divided-by ((x cons) (y cons) &optional new-index)
  "As the defgeneric says, it is an error if y doesn't divide x.
This implementation doesn't signal the error, but silently throws
away the remainder."
  (cons (or new-index (car x))
	(truncate (the integer (cdr x)) (the integer (cdr y)))))

(defmethod sp-pretty-associate ((elt cons))
  (let ((i (car elt))
	(v (cdr elt)))
    (declare (integer v))
    (if (>= v 0)
	(values elt (cons i 1))
      (values (cons i (- v)) (cons i -1)))))      

(defmethod sp-euc-norm ((elt cons))
  (abs (the integer (cdr elt))))

(defmethod sp-neg-closest-quotient ((x cons) (y cons) &optional new-index)
  (cons (or new-index (car x))
	(round (the integer (- (the integer (cdr x))))
	       (the integer (cdr y)))))

(defmethod sp-rounded-rem ((x cons) (y cons) &optional new-index)
  (cons (or new-index (car x))
	(+ (the integer (cdr x))
	   (the integer
	     (* (the integer (cdr y))
		(the integer (round (the integer (- (the integer (cdr x))))
				    (the integer (cdr y)))))))))

(defmethod sp-integrity-check ((elt cons) &key (message ""))
  (assert (typep (car elt) 'fixnum) ()
    "~AIndex ~A not a fixnum." message (car elt))
  (assert (integerp (cdr elt)) ()
    "~AValue ~A not an integer." message (cdr elt)))

(defmethod sp-z-p ((elt cons))
  t)

(defmethod sp-integer-lift ((elt t))
  (cdr elt))

(defmethod sp-integer-value ((elt cons))
  (cdr elt))

;;; Added 3/2/2008 so the 2005 tutorial will work.
(defmacro sp-v (elt) `(the integer (cdr ,elt)))
(defun make-sp (index value) (make-sp-z index value))
(eval-when (:load-toplevel)
  (export 'sp-v)
  (export 'make-sp))
(defmacro from-cons-to-x (elt) elt)
(defmacro from-x-to-cons (x) x)

;;; ---------- Implementation for D = F_p, the field of p elements ----------

(defmacro def-sp-p (p)
  "Given p = 7, for example, a call (def-sp-p 7) to this macro creates
the field F_7 of seven elements.  It defines a sparse-elt structure
sp-7 and implements the generic functions needed for F_7.  The public
constructor is (make-sp-7 index value), which takes any fixnum index
and integer value and reduces the value mod 7 before storing it.  For
any p, values are always stored as integers in the range [0, p).  The
value of p must be known when the macro is expanded, typically at
compile time, and must be a prime integer."
  (assert (and (integerp p) (primep p)) (p)
    "Arg ~A to def-sp-p must be a prime integer." p)
  (when (< p 0) (setq p (- p)))
  (let ((name (intern (format nil "SP-~D" p)))
	(make-name (intern (format nil "MAKE-SP-~D" p)))
	(make-private (intern (format nil "MAKE-SP-~D-PRIVATE" p)))
	(name-i (intern (format nil "SP-~D-I" p)))
	(name-v (intern (format nil "SP-~D-V" p))))
    `(progn
       (defstruct (,name (:constructor ,make-private))
	 ,(format nil "Type of a sparse-elt over F_~D, the field of ~R elements." p p)
	 i v)
       (defmethod ,make-name ((index fixnum) (value integer))
	 ,(format nil "Creates a sparse-elt over F_~D, the field of ~R elements." p p)
	 (,make-private :i index :v (mod (the integer value) ,p)))
       (export (list ',name ',make-name))
       (defmethod copy-sp ((elt ,name) new-index)
	 (,make-private :i new-index :v (,name-v elt)))
       (defmethod sp-print-value ((elt ,name) &optional stream)
	 (format stream "~D" (the (mod ,p) (,name-v elt))))
       (defmethod sp-i-func ((elt ,name))
	 (,name-i elt))
       (defmethod sp-zerop ((elt ,name))
	 (zerop (the (mod ,p) (,name-v elt))))
       (defmethod sp-onep ((elt ,name))
	 (= 1 (the (mod ,p) (,name-v elt))))
       (defmethod sp-neg-one-p ((elt ,name))
	 (= ,(- p 1) (the (mod ,p) (,name-v elt))))
       (defmethod sp-unitp ((elt ,name))
	 (not (zerop (the (mod ,p) (,name-v elt)))))
       (defmethod sp-add ((x ,name) (y ,name) &optional new-index)
	 (,make-private :i (or new-index (,name-i x))
			:v (mod (the (integer 0 ,(- (* 2 p) 2))
				  (+ (the (mod ,p) (,name-v x))
				     (the (mod ,p) (,name-v y))))
				,p)))
       (defmethod sp-subtract ((x ,name) (y ,name) &optional new-index)
	 (,make-private :i (or new-index (,name-i x))
			:v (mod (the (integer ,(- 1 p) ,(- p 1))
				  (- (the (mod ,p) (,name-v x))
				     (the (mod ,p) (,name-v y))))
				,p)))
       (defmethod sp-negate ((elt ,name) &optional new-index)
	 (,make-private :i (or new-index (,name-i elt))
			:v (mod (the (integer ,(- 1 p) 0)
				  (- (the (mod ,p) (,name-v elt))))
				,p)))
       (defmethod sp-mult ((x ,name) (y ,name) &optional new-index)
	 (,make-private :i (or new-index (,name-i x))
			:v (mod (the (integer 0 ,(expt (- p 1) 2))
				  (* (the (mod ,p) (,name-v x))
				     (the (mod ,p) (,name-v y))))
				,p)))
       (defmethod sp-divides ((x ,name) (y ,name))
	 t)
       (defmethod sp-divided-by ((x ,name) (y ,name) &optional new-index)
	 (multiple-value-bind (u v d)
	     (ext-gcd (the (mod ,p) (,name-v y)) ,p)
	   (declare (integer u) (ignore v) (type (integer 0 *) d))
	   (assert (= d 1) ()
	     "Can't invert ~D mod ~D." (,name-v y) ,p)
	   (,make-private :i (or new-index (,name-i x))
			  :v (mod (the integer
				    (* (the (mod ,p) (,name-v x)) u))
				  ,p))))
       (defmethod sp-pretty-associate ((elt ,name))
	 (if (sp-zerop elt)
	     (values elt (sp-embed-z elt 1))
	   (values (sp-embed-z elt 1) elt)))
       (defmethod sp-= ((x ,name) (y ,name))
	 (= (the (mod ,p) (,name-v x)) (the (mod ,p) (,name-v y))))
       (defmethod sp-embed-z ((sample-elt ,name) (value integer)
			      &optional new-index)
	 (,make-private :i (or new-index (,name-i sample-elt))
			:v (mod (the integer value) ,p)))
       (defmethod sp-ring-name ((elt ,name))
	 ,(format nil "F_~D" p))
       (defmethod sp-euc-norm ((elt ,name))
	 (if (zerop (the (mod ,p) (,name-v elt)))
	     0
	   1))
       (defmethod sp-neg-closest-quotient ((x ,name) (y ,name)
					   &optional new-index)
	 (multiple-value-bind (u v d)
	     (ext-gcd (the (mod ,p) (,name-v y)) ,p)
	   (declare (integer u) (ignore v) (type (integer 0 *) d))
	   (assert (= d 1) ()
	     "Can't invert ~D mod ~D." (,name-v y) ,p)
	   (,make-private :i (or new-index (,name-i x))
			  :v (mod (the integer
				    (* -1 (the (mod ,p) (,name-v x)) u))
				  ,p))))
       (defmethod sp-rounded-rem ((x ,name) (y ,name) &optional new-index)
	 "As the defgeneric says, it is an error if y is zero.~&This method doesn't signal the error."
	 (,make-private :i (or new-index (,name-i x)) :v 0))
       (defmethod sp-integrity-check ((elt ,name) &key (message ""))
	 (assert (typep (,name-i elt) 'fixnum) ()
	   "~AIndex ~A not a fixnum for ~A." message (,name-i elt) ,name)
	 (let ((v (,name-v elt)))
	   (assert (and (<= 0 v) (< v ,p)) ()
	     "~AValue ~A out of range [0,~D) for ~A." message v ,p ,name)))
       ;; Use default methods for sp-z-p, sp-integer-value.
       (defmethod sp-integer-lift ((elt ,name))
	 (,name-v elt))
       (defmethod sp-field-p ((elt ,name))
	 t)
       (defmethod sp-f_p-p ((elt ,name))
	 ,p)
       nil)))
	 
;;; -------------------- Unit tests over Z --------------------

(locally (declare (optimize safety))
  (let ((qq (make-sp-z 17 5616))
	(rr (make-sp-z 19 1789)))
    (assert (= (sp-i-func qq) (sp-i qq) 17))
    (assert (= (sp-integer-value qq) (sp-integer-lift qq) 5616))
    (assert (= (sp-i-func rr) (sp-i rr) 19))
    (assert (= (sp-integer-value rr) (sp-integer-lift rr) 1789))
    (assert (equalp qq (sp-embed-z rr 5616 17)))
    (assert (equalp (copy-sp qq 19) (sp-embed-z rr 5616)))
    (assert (and (sp-z-p qq) (sp-z-p rr)
		 (not (sp-z-p "Integer vitae scelerisque purus..."))
		 (not (sp-field-p qq)) (not (sp-f_p-p rr))))
    (and (sp-integrity-check qq) (sp-integrity-check rr))
    (let ((qq23 (copy-sp qq 23)))
      (assert (= (sp-i qq23) 23))
      (assert (= (sp-integer-value qq23) 5616))
      (assert (equalp qq23 (copy-sp qq (+ 13 10)))))
    (assert (eq qq (copy-sp qq 17)))
    (assert (equal (sp-print-value qq) "5616"))
    (let ((ss (make-sp-z 23 -1)))
      (assert (not (sp-zerop ss)))
      (assert (not (sp-onep ss)))
      (assert (sp-neg-one-p ss))
      (assert (sp-unitp ss)))
    (do ((i -3 (1+ i)))
	((> i 3))
      (if (= (abs i) 1)
	  (assert (sp-unitp (make-sp-z 23 i)))
	(assert (not (sp-unitp (make-sp-z 23 i))))))
    (assert (equalp (sp-add qq rr) (make-sp-z 17 (+ 5616 1789))))
    (assert (equalp (sp-add qq rr 23) (make-sp-z 23 (+ 5616 1789))))
    (assert (equalp (sp-subtract qq rr) (make-sp-z 17 (- 5616 1789))))
    (assert (equalp (sp-subtract qq rr 23) (make-sp-z 23 (- 5616 1789))))
    (assert (equalp (sp-negate qq) (make-sp-z 17 -5616)))
    (assert (equalp (sp-negate qq 23) (make-sp-z 23 -5616)))
    (assert (equalp (sp-mult qq rr) (make-sp-z 17 (* 5616 1789))))
    (assert (equalp (sp-mult qq rr 23) (make-sp-z 23 (* 5616 1789))))
    (assert (sp-divides (make-sp-z -1 13) qq))
    (assert (not (sp-divides (make-sp-z -1 97) qq)))
    (assert (equalp (sp-divided-by qq (make-sp-z -1 13)) (make-sp-z 17 432)))
    (assert (equalp (sp-divided-by qq (make-sp-z -1 13) 19) (make-sp-z 19 432)))
    (multiple-value-bind (x y) (sp-pretty-associate (make-sp-z -1 13))
      (assert (equalp x (make-sp-z -1 13)))
      (assert (equalp y (make-sp-z -1 1))))
    (multiple-value-bind (x y) (sp-pretty-associate (make-sp-z -1 -13))
      (assert (equalp x (make-sp-z -1 13)))
      (assert (equalp y (make-sp-z -1 -1))))
    (assert (sp-= (sp-add qq rr) (sp-add rr qq)))
    (assert (not (equalp (sp-add qq rr) (sp-add rr qq))))
    (assert (= 5616 (sp-euc-norm qq) (sp-euc-norm (sp-negate qq))))
    (assert (equalp (sp-neg-closest-quotient qq rr) (make-sp-z 17 -3)))
    (assert (equalp (sp-rounded-rem qq rr) (make-sp-z 17 249)))
    (assert (equalp (sp-neg-closest-quotient qq rr 23) (make-sp-z 23 -3)))
    (assert (equalp (sp-rounded-rem qq rr 23) (make-sp-z 23 249)))
    (assert (equalp (sp-neg-closest-quotient rr qq) (make-sp-z 19 0)))))
