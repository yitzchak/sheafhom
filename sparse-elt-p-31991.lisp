(in-package shh2)

(declaim (optimize speed))

;;; Use this code instead of sparse-elt.lisp (not with it!!) to
;;; hard-code the whole program for the field of order 31991.

(defun make-sp-31991 (index value)
  "Creates a sparse-elt over F_31991, the field of thirty-one thousand
nine hundred ninety-one elements.  It is implemented as a cons
with car a fixnum and cdr an integer in the range [0,31991)."
  (declare (fixnum index) (integer value))
  (cons index (mod value 31991)))

(defun make-sp-z (index value)
  (declare (ignore index value))
  (error "Can't use me: the whole file is hard-coded for F_31991."))

(export (list 'MAKE-SP-31991 'MAKE-SP-Z))

(defmacro sp-i (elt)
  `(the fixnum (car ,elt)))

(defmacro sp-i-func (elt)
  `(sp-i ,elt))

(defmacro sp-v (elt)
  `(the (mod 31991) (cdr ,elt)))

(defmacro copy-sp (elt new-index)
  (with-gensyms (e new-i)
    `(let ((,e ,elt)
	   (,new-i ,new-index))
       (declare (fixnum ,new-i))
       (if (= (sp-i ,e) ,new-i)
	   ,e
	 (cons ,new-i (cdr ,e))))))

(defun sp-print-value (elt &optional stream)
  (format stream "~d" (sp-v elt)))

(defmacro sp-zerop (elt)
  `(zerop (sp-v ,elt)))

(defmacro sp-onep (elt)
  `(= 1 (sp-v ,elt)))

(defmacro sp-neg-one-p (elt)
  `(= 31990 (sp-v ,elt)))

(defmacro sp-unitp (elt)
  `(not (zerop (sp-v ,elt))))

(defun sp-add (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 63980) (+ (sp-v x) (sp-v y))) 31991)))

(defun sp-subtract (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer -31990 31990) (- (sp-v x) (sp-v y))) 31991)))

(defun sp-negate (elt &optional new-index)
  (cons (or new-index (sp-i elt))
	(mod (the (integer -31990 0) (- (sp-v elt))) 31991)))

(defun sp-mult (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 1023360100) (* (sp-v x) (sp-v y))) 31991)))

(defmacro sp-divides (x y)
  (declare (ignore x y))
  't)

(defun sp-divided-by (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 31991)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod ~d." (cdr y) 31991)
    (cons 
     (or new-index (car x)) 
     (mod (the integer (* (sp-v x) u)) 31991))))

(defun sp-pretty-associate (elt)
  (if (sp-zerop elt)
      (values elt (cons (car elt) 1))
    (values (cons (car elt) 1) elt)))

(defmacro sp-= (x y)
  `(= (sp-v ,x) (sp-v ,y)))

(defmacro sp-embed-z (sample-elt value &optional new-index)
  `(cons ,(or new-index `(car ,sample-elt)) (mod (the integer ,value) 31991)))

(defmacro sp-ring-name (elt)
  (declare (ignore elt))
  "F_31991")

(defmacro sp-euc-norm (elt)
  `(the bit (if (zerop (sp-v ,elt)) 0 1)))

(defun sp-neg-closest-quotient (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 31991)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "can't invert ~d mod ~d." (cdr y) 31991)
    (cons 
     (or new-index (car x)) 
     (mod (the integer (- (the integer (* (sp-v x) u)))) 31991))))

(defmacro sp-rounded-rem (x y &optional new-index)
  (declare (ignore y))
  `(cons ,(or new-index `(car ,x)) 0))

(defun sp-integrity-check (elt &key (message ""))
  (let ((v (sp-v elt)))
    (assert (and (<= 0 v) (< v 31991)) ()
      "~AValue ~A out of range [0,31991)." message v)))

(defmacro sp-z-p (elt)
  (declare (ignore elt))
  'nil)

(defun sp-integer-value (elt)
  (declare (ignore elt))
  (error "Can't use me: the whole file is hard-coded for F_31991."))

(defmacro sp-integer-lift (elt)
  `(sp-v ,elt))

(defmacro sp-field-p (elt)
  (declare (ignore elt))
  't)

(defmacro sp-f_p-p (elt)
  (declare (ignore elt))
  '31991)

;;; -------------------- Unit tests --------------------

(dolist (q '(0 1 360 31989 31990))
  (let ((qq (make-sp-31991 17 q)))
    (assert (= (sp-i-func qq) (sp-i qq) 17))
    (assert (sp-field-p qq))
    (assert (aand (sp-f_p-p qq) (= it 31991)))
    (assert (not (sp-z-p qq)))
    (let ((qq23 (copy-sp qq 23)))
      (assert (equalp qq23 (make-sp-31991 23 q)))
      (assert (equalp qq23 (copy-sp qq (+ 13 10)))))
    (assert (eq qq (copy-sp qq 17)))
    (labels ((iff (bool1 bool2) (if bool1 bool2 (not bool2))))
      (assert (iff (sp-zerop qq) (= q 0)))
      (assert (iff (sp-onep qq) (= q 1)))
      (assert (iff (sp-neg-one-p qq) (= q 31990)))
      (assert (iff (sp-unitp qq) (/= q 0)))
      (assert (iff (sp-zerop qq) (zerop (sp-euc-norm qq))))
      (assert (iff (not (sp-zerop qq)) (= 1 (sp-euc-norm qq)))))
    (assert (equalp (sp-negate qq) (make-sp-31991 17 (- q))))
    (assert (equalp (sp-negate qq 23) (make-sp-31991 23 (- q))))
    (multiple-value-bind (x y) (sp-pretty-associate qq)
      (assert (equalp x (make-sp-31991 17 (if (zerop q) 0 1))))
      (assert (equalp y (make-sp-31991 17 (if (zerop q) 1 q)))))
    (dolist (r '(0 1 457 31989 31990)) ;; 31990 = 2*5*7*457
      (let ((rr (make-sp-31991 19 r)))
	(assert (equalp (sp-add qq rr) (make-sp-31991 17 (+ q r))))
	(assert (equalp (sp-add qq rr 23) (make-sp-31991 23 (+ q r))))
	(assert (equalp (sp-subtract qq rr) (make-sp-31991 17 (- q r))))
	(assert (equalp (sp-subtract qq rr 23) (make-sp-31991 23 (- q r))))
	(assert (equalp (sp-mult qq rr) (make-sp-31991 17 (* q r))))
	(assert (equalp (sp-mult qq rr 23) (make-sp-31991 23 (* q r))))
	(unless (sp-zerop rr)
	  (assert (sp-divides rr qq))
	  (assert (equalp qq (sp-mult (sp-divided-by qq rr) rr)))
	  (assert (equalp (copy-sp qq 19)
			  (sp-mult rr (sp-divided-by qq rr))))
	  (assert (equalp (sp-negate qq)
			  (sp-mult (sp-neg-closest-quotient qq rr) rr)))
	  (assert (equalp (sp-negate (copy-sp qq 19))
			  (sp-mult rr (sp-neg-closest-quotient qq rr))))
	  (assert (sp-zerop (sp-rounded-rem qq rr))))
	(assert (sp-= (sp-add qq rr) (sp-add rr qq)))
	(assert (not (equalp (sp-add qq rr) (sp-add rr qq))))))))
