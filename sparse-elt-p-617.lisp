(in-package shh2)

(declaim (optimize safety)) ;; for the low levels

;;; Use this code instead of sparse-elt.lisp (not with it!!) to
;;; hard-code the whole program for the field of order 617.

(defun make-sp-617 (index value)
  "Creates a sparse-elt over F_617, the field of six hundred and
seventeen elements.  It is implemented as a cons with car a fixnum and
cdr an integer in the range [0,617)."
  (declare (fixnum index) (integer value))
  (cons index (mod value 617)))

(defun make-sp-z (index value)
  (declare (ignore index value))
  (error "Can't use me: the whole file is hard-coded for F_617."))

(export (list 'MAKE-SP-617 'MAKE-SP-Z))

(defmacro sp-i (elt)
  `(the fixnum (car ,elt)))

(defmacro sp-i-func (elt)
  `(sp-i ,elt))

(defmacro sp-v (elt)
  `(the (mod 617) (cdr ,elt)))

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
  `(= 616 (sp-v ,elt)))

(defmacro sp-unitp (elt)
  `(not (zerop (sp-v ,elt))))

(defun sp-add (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 1232) (+ (sp-v x) (sp-v y))) 617)))

(defun sp-subtract (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer -616 616) (- (sp-v x) (sp-v y))) 617)))

(defun sp-negate (elt &optional new-index)
  (cons (or new-index (sp-i elt))
	(mod (the (integer -616 0) (- (sp-v elt))) 617)))

(defun sp-mult (x y &optional new-index)
  (cons (or new-index (sp-i x))
	(mod (the (integer 0 379456) (* (sp-v x) (sp-v y))) 617)))

(defmacro sp-divides (x y)
  (declare (ignore x y))
  't)

(defun sp-divided-by (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 617)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 617." (cdr y))
    (cons 
     (or new-index (car x)) 
     (mod (the integer (* (sp-v x) u)) 617))))

(defun sp-pretty-associate (elt)
  (if (sp-zerop elt)
      (values elt (cons (car elt) 1))
    (values (cons (car elt) 1) elt)))

(defmacro sp-= (x y)
  `(= (sp-v ,x) (sp-v ,y)))

(defmacro sp-embed-z (sample-elt value &optional new-index)
  `(cons ,(or new-index `(car ,sample-elt)) (mod (the integer ,value) 617)))

(defmacro sp-ring-name (elt)
  (declare (ignore elt))
  "F_617")

(defmacro sp-euc-norm (elt)
  `(the bit (if (zerop (sp-v ,elt)) 0 1)))

(defun sp-neg-closest-quotient (x y &optional new-index)
  (multiple-value-bind (u v d) (ext-gcd (sp-v y) 617)
    (declare (integer u) (ignore v) (type (integer 1 *) d))
    (assert (= d 1) () "Can't invert ~d mod 617." (cdr y))
    (cons 
     (or new-index (car x)) 
     (mod (the integer (- (the integer (* (sp-v x) u)))) 617))))

(defmacro sp-rounded-rem (x y &optional new-index)
  (declare (ignore y))
  `(cons ,(or new-index `(car ,x)) 0))

(defun sp-integrity-check (elt &key (message ""))
  (let ((v (sp-v elt)))
    (assert (and (<= 0 v) (< v 617)) ()
      "~AValue ~A out of range [0,617)." message v)))

(defmacro sp-z-p (elt)
  (declare (ignore elt))
  'nil)

(defun sp-integer-value (elt)
  (declare (ignore elt))
  (error "Can't use me: the whole file is hard-coded for F_617."))

(defmacro sp-integer-lift (elt)
  `(sp-v ,elt))

(defmacro sp-field-p (elt)
  (declare (ignore elt))
  't)

(defmacro sp-f_p-p (elt)
  (declare (ignore elt))
  '617)
