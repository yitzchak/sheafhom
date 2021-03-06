(in-package shh2)

(declaim (optimize safety debug)) ;; till it's tested

;;; Use this code instead of sparse-elt.lisp (not with it) to
;;; hard-code the whole program for the field of order 12379.

;;; Unlike the sparse-elt-p*.lisp family, the
;;; sparse-elt-[number]x.lisp family encodes index and value in a
;;; single integer (fixnum or bignum).  In this file, we use the low
;;; 14 bits to hold elements of F_12379 as unsigned integers.  [finish
;;; doc...]

(defconstant +mm+ 71372
  "For efficiency, +mm+ should equal m-1, where m is the largest number
of rows to be used by a csparse.  Or +mm+ can be a little bigger.")

(defmacro mm-flip (i)
  `(the fixnum (- +mm+ (the fixnum ,i))))

(defun make-sp-12379 (index value)
  "Creates a sparse-elt over F_12379, the field of twelve thousand
three hundred seventy-nine elements.  The sparse-elt is implemented
as [finish doc...]."
  (declare (fixnum index) (integer value))
  (logior (the integer (ash (mm-flip index) 14))
	  (the (mod 12379) (mod value 12379))))

(eval-when (:load-toplevel)
  (export 'make-sp-12379))

(defun make-sp-z (index value)
  (declare (ignore index value))
  (error "Can't use Z.  You've loaded a file that hard-codes the whole~&program for F_12379."))

(defmacro sp-i (elt)
  `(the fixnum (mm-flip (ash (the integer ,elt) -14))))

(defmethod sp-i-func (elt)
  (sp-i elt))

(defmacro sp-v (elt)
  `(the (mod 12379) (logand (the integer ,elt) #o37777)))

(defmethod copy-sp ((x integer) new-index)
  (make-sp-12379 new-index (sp-v x)))

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
  (make-sp-12379 (or new-index (sp-i x))
		 (the (integer 0 24756) (+ (sp-v x) (sp-v y)))))

(defun sp-subtract (x y &optional new-index)
  (make-sp-12379 (or new-index (sp-i x))
		 (the (integer -12378 12378) (- (sp-v x) (sp-v y)))))

(defun sp-negate (elt &optional new-index)
  (make-sp-12379 (or new-index (sp-i elt))
		 (the (integer -12378 0) (- (sp-v elt)))))

(defun sp-mult (x y &optional new-index)
  (make-sp-12379 (or new-index (sp-i x))
		 (the (integer 0 153214884) (* (sp-v x) (sp-v y)))))

(defmacro sp-divides (x y)
  (declare (ignore x y))
  't)

(defun sp-divided-by (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 12379)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 12379." (sp-v y))
    (make-sp-12379 (or new-index (sp-i x)) (* (sp-v x) u))))

(defun sp-pretty-associate (elt)
  (if (sp-zerop elt)
      (values elt (make-sp-12379 (sp-i elt) 1))
    (values (make-sp-12379 (sp-i elt) 1) elt)))

(defmacro sp-= (x y)
  `(= (sp-v ,x) (sp-v ,y)))

(defmacro sp-embed-z (sample-elt value &optional new-index)
  `(make-sp-12379 ,(or new-index `(sp-i ,sample-elt)) ,value))

(defmacro sp-ring-name (elt)
  (declare (ignore elt))
  "F_12379")

(defmacro sp-euc-norm (elt)
  `(the bit (if (zerop (sp-v ,elt)) 0 1)))

(defun sp-neg-closest-quotient (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 12379)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 12379." (sp-v y))
    (make-sp-12379 (or new-index (sp-i x)) (- (the integer (* (sp-v x) u))))))

(defmacro sp-rounded-rem (x y &optional new-index)
  (declare (ignore y))
  `(make-sp-12379 ,(or new-index `(sp-i ,x)) 0))

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

;;; ------------------------------------------------------------

;;; Temp macros while in transition between cons-based and
;;; integer-based sparse-elts.

(defmacro from-x-to-cons (x)
  `(cons (sp-i ,x) (sp-v ,x)))

(defmacro from-cons-to-x (c)
  `(make-sp-12379 (car ,c) (cdr ,c)))
