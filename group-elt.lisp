(in-package shh2)

;;; -------------------- Contract for group-elt --------------------

;;; Subclasses of group-elt must implement the generic functions in
;;; this contract section, including hash-key.  They may also want to
;;; implement other generic functions in this class, as well as
;;; print-object.

(defclass group-elt ()
  ()
  (:documentation "A group-elt is an object g supporting the group operations (mult-two g h) and (inverse g), with (group-elt-equal g h) giving an appropriate notion of equality.  It must also support identity-elt and identityp.  It must support hash-key, because you never know when the system will use it internally in a hash-group."))

(defgeneric mult-two (g1 g2)
  (:documentation "Multiplication of two group-elts.  The recommended way to multiply group-elts is with mult, which takes any positive number of arguments."))

(defgeneric inverse (g)
  (:documentation "The inverse of a group-elt."))

(defgeneric identity-elt (x)
  (:documentation "If x is a group-elt, returns an identity element of the same class, up to group-elt-equal.  If x is a group, return an identity element for the group."))

(defgeneric identityp (g)
  (:documentation "Whether g is the identity element among group-elts of its class."))

;;; ------------------------- Group-elt functions -------------------------

(defmacro mult (&rest args)
  "Multiplies one or more group-elts.  E.g., turns (mult a b c) into (mult-two a (mult-two b c))."
  (if (null (cdr args))
      (car args)
    `(mult-two ,(car args) (mult ,@(cdr args)))))      
      
(defgeneric group-elt-equal (g1 g2)
  (:documentation "Whether two group-elts are equal."))

(defmethod group-elt-equal ((g1 group-elt) (g2 group-elt))
  "Default implementation saying elements are equal if and only if they have the same hash-key.  This allows you to use the elements in a hash-group."
  (equalp (hash-key g1) (hash-key g2)))

(defgeneric commutes-with (g1 g2)
  (:documentation "Whether two group-elts commute."))

(defmethod commutes-with ((g1 group-elt) (g2 group-elt))
  (group-elt-equal (mult g1 g2) (mult g2 g1)))

(defgeneric conj-y-x-yinv (x y &optional yinv)
  (:documentation "Given group-elts x and y, returns y x y^-1.  You can optionally pass in y^-1 as yinv."))

(defmethod conj-y-x-yinv ((x group-elt) (y group-elt) &optional (yinv (inverse y)))
  (mult y x yinv))

(defgeneric conj-yinv-x-y (x y &optional yinv)
  (:documentation "Given group-elts x and y, returns y^-1 x y.  You can optionally pass in y^-1 as yinv."))

(defmethod conj-yinv-x-y ((x group-elt) (y group-elt) &optional (yinv (inverse y)))
  (mult yinv x y))

(defgeneric power (x i)
  (:documentation "Returns the power x^i.  Also see (power-mod x i n)."))

(defmethod power ((g group-elt) (i integer))
  (if (< i 0)
      (power (inverse g) (- i))
    (if (= i 1)
	g
      (labels ((power-aux (g i ans)
		 (declare (type (integer 0 *) i))
		 (if (zerop i)
		     ans
		   (multiple-value-bind (q r) (floor i 2)
		     (declare (type (integer 0 *) q)
			      (type (integer 0 1) r))
		     (power-aux (mult g g)
				q
				(if (= r 0) ans (mult g ans)))))))
	(power-aux g i (identity-elt g))))))
		 
;;; -------------------- Commuting-group-elt --------------------

(defclass commuting-group-elt (group-elt)
  ()
  (:documentation "A subclass of group-elt can extend from this if multiplication is always commutative in that class."))

(defmethod commutes-with ((g1 commuting-group-elt) (g2 commuting-group-elt))
  t)

(defmethod conj-y-x-yinv ((x commuting-group-elt) (y commuting-group-elt) &optional yinv)
  (declare (ignore yinv))
  x)

(defmethod conj-yinv-x-y ((x commuting-group-elt) (y commuting-group-elt) &optional yinv)
  (declare (ignore yinv))
  x)

;;; -------------------- The mod-1 group-elt --------------------

(defclass mod-1 (commuting-group-elt)
  ((value :initarg :value :initform 0 :type rational))
  ;; value must be in [0,1).  make-mod-1 does this automatically.
  (:documentation "An element of the group of rational numbers modulo 1 under addition.  That is, an element of Q/Z.  The mod-1 with value 1/n generates a cyclic group of order n--see the class cyclic-group."))

(defun make-mod-1 (v)
  "Creates a mod-1 with value v mod 1."
  (declare (rational v))
  (make-instance 'mod-1 :value (mod v 1)))

(defmethod mult-two ((g1 mod-1) (g2 mod-1))
  (with-slots ((v1 value)) g1
    (declare (rational v1))
    (with-slots ((v2 value)) g2
      (declare (rational v2))
      (make-mod-1 (+ v1 v2)))))

(defmethod inverse ((g mod-1))
  (with-slots (value) g
    (declare (rational value))
    (make-mod-1 (- value))))

(defmethod identity-elt ((g mod-1))
  (make-mod-1 0))

(defmethod identityp ((g mod-1))
  (with-slots (value) g
    (declare (rational value))
    (zerop value)))

(defmethod hash-key ((g mod-1))
  (with-slots (value) g
    value))

(defmethod group-elt-equal ((g1 mod-1) (g2 mod-1))
  (with-slots ((v1 value)) g1
    (declare (rational v1))
    (with-slots ((v2 value)) g2
      (declare (rational v2))
      (= v1 v2))))

(defmethod power ((g mod-1) (i integer))
  (with-slots (value) g
    (declare (rational value))
    (make-mod-1 (* value i))))

(defmethod print-object ((g mod-1) s)
  (with-slots (value) g
    (declare (rational value))
    (format s "#<~S mod 1>" value)))

;;; -------------------- Semidirect and direct products --------------------

;;; G = H x| K, where x| is the symbol

;;; \  /|
;;;  \/ |
;;;  /\ |
;;; /  \|

;;; Example: the dihedral group of order 2n is C_n x| C_2 with
;;; action = #'(lambda (k1 h2) (if (identityp k1) h2 (inverse h2))).

;;; Example: if G is given and H, K are subgroups with H normal, then
;;; action = #'(lambda (k1 h2) (conj-y-x-yinv h2 k1)).

(defgeneric factor1 (g-or-gg)
  (:documentation "When applied to a semidirect-product group or direct-product group, this returns the first factor.  When applied to the elements of such groups, this is the homomorphism onto the first factor."))

(defgeneric factor2 (g-or-gg)
  (:documentation "When applied to a semidirect-product group or direct-product group, this returns the second factor.  When applied to the elements of such groups, this is the mapping onto the second factor; it is a homomorphism if the product is direct."))

(defclass semidirect-product-elt (group-elt)
  ((h :reader factor1
      :initarg :h
      :type group-elt)
   (k :reader factor2
      :initarg :k
      :type group-elt)
   (action :initarg :action
	   :type function
	   :documentation "Takes arguments (k1 h2), meaning there is a homomorphism sigma from K to Aut(H) and k1 acts on H by sigma_k1.  The return value for action is sigma_k1(h2)."))
  ;; It would be more elegant for 'action' to map k1 to a function of
  ;; one variable sigma_k1 and have the latter act on h2.  But that
  ;; would mean keeping |K| functions hanging around or creating them
  ;; on the fly.
  (:documentation "An element of the semidirect product H x| K.  See also factor1, factor2."))

(defun make-semidirect-product-elt (h k action)
  (make-instance 'semidirect-product-elt
    :h h :k k :action action))

(defmethod mult-two ((g1 semidirect-product-elt) (g2 semidirect-product-elt))
  (with-slots ((h1 h) (k1 k) action) g1
    (with-slots ((h2 h) (k2 k)) g2
      (make-semidirect-product-elt
       (mult h1 (funcall action k1 h2))
       (mult k1 k2)
       action))))

(defmethod inverse ((g semidirect-product-elt))
  (with-slots (h k action) g
    (make-semidirect-product-elt
     (funcall action k (inverse h))
     (inverse k)
     action)))

(defmethod identity-elt ((g semidirect-product-elt))
  (with-slots (h k action) g
    (make-semidirect-product-elt
     (identity-elt h)
     (identity-elt k)
     action)))

(defmethod identityp ((g semidirect-product-elt))
  (with-slots (h k) g
    (and (identityp h) (identityp k))))

(defmethod hash-key ((g semidirect-product-elt))
  (with-slots (h k) g
    (cons (hash-key h) (hash-key k))))

(defmethod group-elt-equal ((g1 semidirect-product-elt) (g2 semidirect-product-elt))
  (with-slots ((h1 h) (k1 k)) g1
    (with-slots ((h2 h) (k2 k)) g2
      (and (group-elt-equal h1 h2) (group-elt-equal k1 k2)))))

(defmethod print-object ((g semidirect-product-elt) s)
  (with-slots (h k) g
    (format s "(~S x| ~S)" h k)))

(defclass direct-product-elt (semidirect-product-elt)
  ()
  (:documentation "A semidirect-product-elt where the action is guaranteed to be trivial."))

(defvar *trivial-action* #'(lambda (k h) (declare (ignore k)) h))

(defun make-direct-product-elt (h k)
  (make-instance 'direct-product-elt
    :h h :k k :action *trivial-action*))

(defmethod mult-two ((g1 direct-product-elt) (g2 direct-product-elt))
  (with-slots ((h1 h) (k1 k)) g1
    (with-slots ((h2 h) (k2 k)) g2
      (make-direct-product-elt (mult h1 h2) (mult k1 k2)))))

(defmethod inverse ((g direct-product-elt))
  (with-slots (h k) g
    (make-direct-product-elt (inverse h) (inverse k))))

(defmethod identity-elt ((g direct-product-elt))
  (with-slots (h k) g
    (make-direct-product-elt (identity-elt h) (identity-elt k))))

(defmethod commutes-with ((g1 direct-product-elt) (g2 direct-product-elt))
  (with-slots ((h1 h) (k1 k)) g1
    (with-slots ((h2 h) (k2 k)) g2
      (and (commutes-with h1 h2) (commutes-with k1 k2)))))

(defmethod conj-y-x-yinv ((x direct-product-elt) (y direct-product-elt) &optional (yinv (inverse y)))
  (with-slots ((h1 h) (k1 k)) x
    (with-slots ((h2 h) (k2 k)) y
      (with-slots ((h2inv h) (k2inv k)) yinv
	(make-direct-product-elt (conj-y-x-yinv h1 h2 h2inv)
				 (conj-y-x-yinv k1 k2 k2inv))))))

(defmethod conj-yinv-x-y ((x direct-product-elt) (y direct-product-elt) &optional (yinv (inverse y)))
  (with-slots ((h1 h) (k1 k)) x
    (with-slots ((h2 h) (k2 k)) y
      (with-slots ((h2inv h) (k2inv k)) yinv
	(make-direct-product-elt (conj-yinv-x-y h1 h2 h2inv)
				 (conj-yinv-x-y k1 k2 k2inv))))))

(defmethod power ((g direct-product-elt) (i integer))
  (with-slots (h k) g
    (make-direct-product-elt (power h i) (power k i))))
  
(defmethod print-object ((g direct-product-elt) s)
  (with-slots (h k) g
    (format s "(~S x ~S)" h k)))

