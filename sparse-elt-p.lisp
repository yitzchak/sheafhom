(in-package shh2)

(declaim (optimize speed))

;;; Use this code instead of sparse-elt.lisp (not with it) to
;;; hard-code the whole program for the field of order 12379.

;;; The file sparse-elt.lisp creates functions, such as sp-add for
;;; addition, that support different implementations for different
;;; domains in the same runtime session.  By contrast,
;;; sparse-elt-p.lisp assumes only the field F_12379 is in use, and it
;;; replaces many functions with macros for the sake of speed.  This
;;; is why we say, don't load both files at the same time.

(defun make-sp-12379 (index value)
  "Creates a sparse-elt over F_12379, the field of twelve thousand
three hundred seventy-nine elements.  The sparse-elt is implemented
as a cons with car a fixnum and cdr an integer in [0,12379)."
  (declare (integer value))
  (cons index (mod value 12379)))

(eval-when (:load-toplevel)
  (export 'make-sp-12379))

(defun make-sp-z (index value)
  (declare (ignore index value))
  (error "Can't use Z.  You've loaded a file that hard-codes the whole~&program for F_12379."))

(defmacro sp-i (elt)
  `(the fixnum (car ,elt)))

(defmacro sp-i-func (elt)
  `(sp-i ,elt))

(defmacro sp-v (elt)
  `(the (mod 12379) (cdr ,elt)))

(defmethod copy-sp ((x cons) new-index)
  (cons new-index (cdr x)))

(defun sp-print-value (elt &optional stream)
  (format stream "~d" (sp-v elt)))

(defmacro sp-zerop (elt)
  `(zerop (sp-v ,elt)))

(defmacro sp-onep (elt)
  `(= 1 (sp-v ,elt)))

(defmacro sp-neg-one-p (elt)
  `(= 12378 (sp-v ,elt)))

(defmacro sp-unitp (elt)
  `(not (zerop (sp-v ,elt))))

(defun sp-add (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 24756) (+ (sp-v x) (sp-v y))) 12379)))

(defun sp-subtract (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer -12378 12378) (- (sp-v x) (sp-v y))) 12379)))

(defun sp-negate (elt &optional new-index)
  (cons (or new-index (sp-i elt))
	(mod (the (integer -12378 0) (- (sp-v elt))) 12379)))

(defun sp-mult (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 153214884) (* (sp-v x) (sp-v y))) 12379)))

(defmacro sp-divides (x y)
  (declare (ignore x y))
  't)

(defun sp-divided-by (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 12379)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 12379." (cdr y))
    (cons 
     (or new-index (car x)) 
     (mod (the integer (* (sp-v x) u)) 12379))))

(defun sp-pretty-associate (elt)
  (if (sp-zerop elt)
      (values elt (cons (car elt) 1))
    (values (cons (car elt) 1) elt)))

(defmacro sp-= (x y)
  `(= (sp-v ,x) (sp-v ,y)))

(defmacro sp-embed-z (sample-elt value &optional new-index)
  `(cons ,(or new-index `(car ,sample-elt)) (mod (the integer ,value) 12379)))

(defmacro sp-ring-name (elt)
  (declare (ignore elt))
  "F_12379")

(defmacro sp-euc-norm (elt)
  `(the bit (if (zerop (sp-v ,elt)) 0 1)))

(defun sp-neg-closest-quotient (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 12379)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 12379." (cdr y))
    (cons 
     (or new-index (car x)) 
     (mod (the integer (- (the integer (* (sp-v x) u)))) 12379))))

(defmacro sp-rounded-rem (x y &optional new-index)
  (declare (ignore y))
  `(cons ,(or new-index `(car ,x)) 0))

(defun sp-integrity-check (elt &key (message ""))
  (let ((v (sp-v elt)))
    (assert (and (<= 0 v) (< v 12379)) ()
      "~AValue ~A out of range [0,12379)." message v)))

(defmacro sp-z-p (elt)
  (declare (ignore elt))
  'nil)

(defun sp-integer-value (elt)
  (declare (ignore elt))
  (error "Can't use me: the whole file is hard-coded for F_12379."))

(defmacro sp-integer-lift (elt)
  `(sp-v ,elt))

(defmacro sp-field-p (elt)
  (declare (ignore elt))
  't)

(defmacro sp-f_p-p (elt)
  (declare (ignore elt))
  '12379)
