(in-package shh2)

(declaim (optimize safety debug)) ;; for now

;;; -------------------- Additive categories --------------------

(defclass add-cat-obj (cat-obj)
  ()
  (:documentation "An object in an additive category."))

(defclass add-cat-mfm (cat-mfm)
  ()
  (:documentation "A morphism in an additive category."))

(defgeneric make-zero-obj (x)
  (:documentation "Returns a zero object in x's category."))

(defgeneric make-zero-mfm (sou tar)
  (:documentation "Returns the zero morphism from sou to tar."))

(defgeneric add-cat-zerop (x)
  (:documentation "Whether x is a zero object or morphism."))

(defgeneric add (f &rest more-fs)
  (:documentation "Returns the sum of one or more add-cat-mfm's.
Non-destructive to the underlying data.  Each primary method
for add should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments.  The :before method checks whether
the sources and targets match."))

(defgeneric subtract (f &rest more-fs)
  (:documentation "Returns the difference of one or more
add-cat-mfm's.  E.g., (subtract f g h) is f - g - h.
Non-destructive to the underlying data.  Each primary method
for subtract should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments.  The :before method checks whether
the sources and targets match."))

(defgeneric composition-zerop (f g)
  (:documentation "Whether the composition
   <---f--- <---g---
is zero.  Gives the same result
as (add-cat-zerop (compose f g)), but may be more efficient
because it doesn't have to create the composition."))

(defclass direct-sum (add-cat-obj)
  ((summands :reader summands :initarg :summands :type list
	     :documentation "The list of summand objects in the sum."))
  (:documentation "The direct sum [and direct product--they're the
same] of the objects in 'summands'."))

(defgeneric mfm-from-direct-sum (sum tar mfm-list)
  (:documentation "Given a list of morphisms from the summands
to tar, this returns the morphism from the sum to tar."))

(defgeneric mfm-to-direct-sum (sou sum mfm-list)
  (:documentation "Given a list of morphisms from sou to the
summands, this returns the morphism from sou to the sum."))

;;; - - - - - - - - - - Partial Implementations - - - - - - - - - - -

(defmethod add :around ((f add-cat-mfm) &rest more-fs)
  "Each primary method for add should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments."
  (if (endp more-fs)
      f
    (let ((f-plus-g (call-next-method f (list (first more-fs)))))
      (apply #'add (cons f-plus-g (rest more-fs))))))

(defmethod add :before ((f add-cat-mfm) &rest more-fs)
  "Checks first whether the sources and targets match."
  (let ((g (first more-fs)))
    (assert (cat-equal-p (sou f) (sou g)) (f g) "Unequal sources.")
    (assert (cat-equal-p (tar f) (tar g)) (f g) "Unequal targets.")))

(defmethod subtract :around ((f add-cat-mfm) &rest more-fs)
  "Each primary method for subtract should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments."
  (if (endp more-fs)
      f
    (let ((f-minus-g (call-next-method f (list (first more-fs)))))
      (apply #'subtract (cons f-minus-g (rest more-fs))))))

(defmethod subtract :before ((f add-cat-mfm) &rest more-fs)
  "Checkes first whether the sources and targets match."
  (let ((g (first more-fs)))
    (assert (cat-equal-p (sou f) (sou g)) (f g) "Unequal sources.")
    (assert (cat-equal-p (tar f) (tar g)) (f g) "Unequal targets.")))

(defmethod composition-zerop :before ((f add-cat-mfm) (g add-cat-mfm))
  "Checks first whether the inner objects match."
  (assert (cat-equal-p (sou f) (tar g)) (f g)
    "Objects in the middle of the composition are unequal."))

(defmethod composition-zerop ((f add-cat-mfm) (g add-cat-mfm))
  "Default implementation that creates the composition."
  (add-cat-zerop (compose f g)))

(defmethod cat-equal-p ((x direct-sum) (y direct-sum))
  "Whether the summands are equal term by term."
  (labels ((aux (list-x list-y)
	     (cond ((endp list-x) (endp list-y))
		   ((endp list-y) nil)
		   ((cat-equal-p (first list-x) (first list-y))
		    (aux (rest list-x) (rest list-y)))
		   (t nil))))
    (aux (summands x) (summands y))))

;;; --------------- Abelian categories ---------------

(defclass abelian-cat-obj (add-cat-obj)
  ()
  (:documentation "An object in an abelian category."))

(defclass abelian-cat-mfm (add-cat-mfm)
  ()
  (:documentation "A morphism in an abelian category."))

(defgeneric ker (f)
  (:documentation "Returns the kernel of the mfm f."))

(defgeneric pullback-to-ker (g f)
  (:documentation "In the call (pullback-to-ker g f),
the arguments f, g are morphisms,
with fg = 0.  Output is a morphism h from (sou g) to (sou (ker f))
such that (compose (ker f) h) is the same as g.  Mnemonic: pull g back
to the kernel of f."))

(defgeneric coker (f)
  (:documentation "Returns the cokernel of the mfm f."))

(defgeneric pushforward-to-coker (g f)
  (:documentation "In the call (pushforward-to-coker g f),
the arguments f, g are morphisms,
with gf = 0.  Output is a morphism h from (tar (coker f))
to (tar g) such that (compose h (coker f)) is the same as g.
Mnemonic: push g forward to the cokernel of f."))

;;; An image is a kernel for a cokernel.  A coimage is a cokernel for
;;; a kernel.  There is a canonical map from coimage to image, and a
;;; central abelian category axiom says this map is an isomorphism.
;;; We can implement these later, deciding what auxiliary parameters
;;; to pass (sources, targets, ...), if any.

;;; ----- Finitely-generated free Z-modules, an additive category -----

(defclass free-z-module (add-cat-obj)
  ((rank :type (integer 0 *) :reader rank :initarg :rank))
  (:documentation "A free Z-module of the indicated rank.
To construct one, use make-free-z-module, because it uses
a canonical copy of the 0 module."))

(defclass free-z-mfm (add-cat-mfm)
  ()
  (:documentation "A morphism of free-z-modules."))

(defclass free-z-module-direct-sum (free-z-module direct-sum)
  ()
  (:documentation "A direct sum of free Z-modules."))

(defvar *free-z-zero-module* nil ;; evaluated lazily
  "A standard copy the zero free-z-module.")

(defun make-free-z-module (r)
  "Creates a free-z-module of rank r."
  (declare (type (integer 0 *) r))
  (if (zerop r)
      (aif *free-z-zero-module*
	   it
	(setq *free-z-zero-module* (make-instance 'free-z-module :rank 0)))
    (make-instance 'free-z-module :rank r)))

(defun make-free-z-module-direct-sum (&rest free-z-objs)
  (assert (every #'(lambda (x) (typep x 'free-z-module)) free-z-objs) ()
    "Some summands are not free-z-modules:~&  ~S" free-z-objs)
  (make-instance 'free-z-module-direct-sum
    :rank (apply #'+ (mapcar #'rank free-z-objs))
    :summands (copy-list free-z-objs)))
      
;;; - - - - - csparsez-mfm and its private methods - - - - -

(defclass csparsez-mfm (free-z-mfm)
  ((mat :type (or csparse null) :initarg :mat)
   (snf-args :type list :initform (list :use-p :use-q))
   (snf :type (or snf null) :initform nil))
  (:documentation "A morphism of free Z-modules determined
by a csparse [a sparse matrix] whose underlying integral
domain is Z.  The csparse should be m-by-n, where n is
the rank of the source and m the rank of the target.  If
the underlying SNF is created destructively [see
destroy-matrix], subsequent calls to (mat ...) will signal
an error."))
;; At first, the csparse is stored in mat, and snf is nil.  Later, if
;; exact category stuff is required, the snf is stored in snf, and mat
;; is set to nil.  If the snf is created non-destructively, it
;; maintains its own copy of mat.  The methods
;; allow-[...]-coord-changes and destroy-matrix, called before snf is
;; created, can specify whether or not the snf is created
;; destructively, and whether P's and Q's are stored.  The elements of
;; snf-args correspond to "t" arguments to make-snf; elements can be
;; :use-p, :use-q, :destructive-p.

(defmethod make-csparsez-mfm ((sou free-z-module) (tar free-z-module) (mat csparse))
  (make-instance 'csparsez-mfm :sou sou :tar tar :mat mat))

(defmethod make-csparsez-mfm ((sou free-z-module) (tar free-z-module) (snf0 snf))
  (let ((ans (make-instance 'csparsez-mfm :sou sou :tar tar :mat nil)))
    (setf (slot-value ans 'snf) snf0
	  (slot-value ans 'snf-args) '())
    ans))

(defgeneric allow-sou-coord-changes (f)
  (:documentation
   "Let f be a free-z-mfm.
When we compute the SNF of f's underlying matrix, this
directs the algorithm not to save the change-of-coordinate
matrices on the source side, the Q's.  Returns f.
If f has no stored SNF, passes f through unchanged."))

(defmethod allow-sou-coord-changes ((f csparsez-mfm))
  (with-slots (snf) f
    (unless snf
      (with-slots (snf-args) f
	(setq snf-args (delete :use-q snf-args)))))
  f)

(defgeneric allow-tar-coord-changes (f)
  (:documentation
   "Let f be a free-z-mfm.
When we compute the SNF of f's underlying matrix, this
directs the algorithm not to save the change-of-coordinate
matrices on the target side, the P's.  Returns f.
If f has no stored SNF, passes f through unchanged."))

(defmethod allow-tar-coord-changes ((f csparsez-mfm))
  (with-slots (snf) f
    (unless snf
      (with-slots (snf-args) f
	(setq snf-args (delete :use-p snf-args)))))
  f)

(defgeneric destroy-matrix (f)
  (:documentation
   "Let f be a free-z-mfm.
When we compute the SNF of f's underlying matrix, this
directs the algorithm to work destructively, not preserving
a copy of the underlying matrix.  Returns f.
If f has no stored SNF, passes f through unchanged."))

(defmethod destroy-matrix ((f csparsez-mfm))
  (with-slots (snf) f
    (unless snf
      (with-slots (snf-args) f
	(pushnew :destructive-p snf-args))))
  f)

(defgeneric do-snf-if-nec (f)
  (:documentation
   "Fills in f's snf slot if that hasn't been done yet.  Returns f."))

(defmethod do-snf-if-nec ((f csparsez-mfm))
  (with-slots (snf) f
    (unless snf
      (with-slots (mat) f
	(assert (not (null mat)) (f)
	  "Morphism was created with a null underlying matrix.")
	(with-slots (snf-args) f
	  (setq snf (make-snf mat
			      (member :use-p snf-args)
			      (member :use-q snf-args)
			      (member :destructive-p snf-args))
		mat nil
		snf-args '())
	  f)))))

(defmethod mat ((f csparsez-mfm))
  "If the underlying SNF is created destructively
[see destroy-matrix], subsequent calls to (mat ...) will
signal an error."
  (with-slots (mat) f
    (aif mat
	 it
      (with-slots (snf) f
	(assert (not (null snf)) (f)
	  "Morphism was created with a null underlying matrix.")
	(aif (mat snf)
	     it
	  (assert nil (f)
	    "Morphism has no underlying matrix.~&Was its SNF computed destructively?"))))))

(defmethod integrity-check ((f csparsez-mfm) &key (message ""))
  (with-slots (mat snf) f
    (when mat
      (integrity-check mat :message message))
    (when snf
      (with-slots (use-p use-q) snf
	(if (and use-p use-q)
	    (integrity-check snf :message message :orig mat)
	  (integrity-check snf :message message :orig nil))))))  

(defmethod assert-has-p ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (with-slots (use-p) snf
      (assert use-p (f)
	"The SNF was computed without remembering the~&changes of coords on the target side."))))
    
(defmethod assert-has-q ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (with-slots (use-q) snf
      (assert use-q (f)
	"The SNF was computed without remembering the~&changes of coords on the source side."))))
    
;;; - - - - - - - - - - free-z-zero-mfm - - - - - - - - - -

(defclass free-z-zero-mfm (free-z-mfm)
  ()
  (:documentation "A zero morphism between free-z-modules.
To construct one, use make-zero-mfm."))

(defmethod make-zero-mfm ((sou free-z-module) (tar free-z-module))
  (make-instance 'free-z-zero-mfm :sou sou :tar tar))

;; Be suspicious if this is called.  The whole point of
;; free-z-zero-mfm is to avoid allocating large empty matrices.
(defmethod mat ((f free-z-zero-mfm))
  (make-csparse-zero (rank (tar f)) (rank (sou f))))

(defmethod allow-sou-coord-changes ((f free-z-zero-mfm))
  f)

(defmethod allow-tar-coord-changes ((f free-z-zero-mfm))
  f)

(defmethod destroy-matrix ((f free-z-zero-mfm))
  f)

(defmethod do-snf-if-nec ((f free-z-zero-mfm))
  '())

;;; ----- Implementation of free-z-module/mfm as an additive category -----

(defmethod make-free-z-mfm ((so free-z-module) (ta free-z-module) (ma csparse))
  "Makes a csparsez-mfm, or a free-z-zero-mfm when it can."
  (with-csparse-slots (m n) ma
    (assert (= n (rank so)) () "Rank mismatch in source.")
    (assert (= m (rank ta)) () "Rank mismatch in target.")
    (if (m-zerop ma)
	(make-instance 'free-z-zero-mfm :sou so :tar ta)
      (make-csparsez-mfm so ta ma))))

(defmethod integrity-check ((f free-z-mfm) &key (message ""))
  "Default method for free-z-mfm that doesn't check anything."
  (declare (ignore message))
  nil)

(defmethod cat-equal-p ((x free-z-module) (y free-z-module))
  "A strict definition: x and y must be exactly the same object."
  (eq x y))

(defmethod cat-equal-p :around ((f free-z-mfm) (g free-z-mfm))
  (and (cat-equal-p (sou f) (sou g))
       (cat-equal-p (tar f) (tar g))
       (call-next-method f g)))

(defmethod cat-equal-p ((f csparsez-mfm) (g csparsez-mfm))
  (equalp (the csparse (mat f)) (the csparse (mat g))))

(defmethod cat-equal-p ((f free-z-mfm) (g free-z-zero-mfm))
  (add-cat-zerop f))

(defmethod cat-equal-p ((f free-z-zero-mfm) (g free-z-mfm))
  (add-cat-zerop g))

(defmethod make-id-mfm ((x free-z-module))
  (with-slots ((r rank)) x
    (if (zerop r)
	(make-zero-mfm x x)
      (make-free-z-mfm x x (make-zero-and-id r r 0 0 r #'make-sp-z)))))

(defmethod id-mfm-p ((f csparsez-mfm))
  (m-id-p (mat f)))

(defmethod id-mfm-p ((f free-z-zero-mfm))
  (add-cat-zerop (sou f)))

(defmethod compose ((f csparsez-mfm) &rest more-fs)
  "Uses non-destructive matrix multiplication."
  (let ((g (first more-fs)))
    (declare (type free-z-mfm g))
    (etypecase g
      (csparsez-mfm
       (make-free-z-mfm (sou g) (tar f) (m-mult (mat f) (mat g))))
      (free-z-zero-mfm
       (make-zero-mfm (sou g) (tar f))))))

(defmethod compose ((f free-z-zero-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (declare (type free-z-mfm g))
    (make-zero-mfm (sou g) (tar f))))

(defmethod composition-zerop ((f csparsez-mfm) (g csparsez-mfm))
  (m-product-zerop (mat f) (mat g)))

(defmethod composition-zerop ((f free-z-zero-mfm) (g free-z-mfm))
  t)

(defmethod composition-zerop ((f free-z-mfm) (g free-z-zero-mfm))
  t)

;;; The whole story of the derived category is in why monic-p uses
;;; rank and epic-p uses num-units....

(defmethod monic-p ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (= (rank snf) (rank (sou f)))))

(defmethod epic-p ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (= (num-units snf) (rank (tar f)))))

(defmethod monic-p ((f free-z-zero-mfm))
  (add-cat-zerop (sou f)))

(defmethod epic-p ((f free-z-zero-mfm))
  (add-cat-zerop (tar f)))

(defmethod isomorphism-p ((f free-z-mfm))
  (and (monic-p f) (epic-p f)))

(defmethod make-inverse-mfm ((f csparsez-mfm))
  (assert-has-p f)
  (assert-has-q f)
  (with-slots (snf) f
    (with-slots (d) snf
      (let ((n (rank (sou f))))
	(declare (integer n))
	(assert (= n (rank (tar f))) (f)
	  "Can't invert: the matrix isn't square.")
	(assert (= n (rank snf)) (f)
	  "Can't invert: the matrix doesn't have full rank.")
	(assert (= n (num-units snf)) (f)
	  "Can't invert over Z, though could over Q.")
	(let ((ans (make-zero-and-id n n 0 0 n #'make-sp-z)))
	  (declare (type csparse ans))
	  (do-snf-q-rev (q snf)
	    (m-mult ans (m-inverse q)))
	  (dotimes-f (j n)
	    (when (sp-neg-one-p (csparse-get d j j))
	      (negate-col ans j)))
	  (do-snf-p-rev (p snf)
	    (m-mult ans (m-inverse p)))
	  ;; Better(?): also set result's snf.
	  (make-free-z-mfm (tar f) (sou f) ans))))))

(defmethod make-inverse-mfm ((f free-z-zero-mfm))
  (assert (add-cat-zerop (sou f)) (f)
    "Can't invert a zero morphism with a non-zero source.")
  (assert (add-cat-zerop (tar f)) (f)
    "Can't invert a zero morphism with a non-zero target.")
  (make-zero-mfm (tar f) (sou f)))

(defmethod add ((f csparsez-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (make-free-z-mfm (sou f) (tar f) (m-add (mat f) (mat g)))))

(defmethod add ((f free-z-zero-mfm) &rest more-fs)
  (first more-fs))

(defmethod subtract ((f csparsez-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (make-free-z-mfm (sou f) (tar f) (m-subtract (mat f) (mat g)))))

(defmethod subtract ((f free-z-zero-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (declare (type free-z-mfm g))
    (etypecase g
      (csparsez-mfm
       (make-free-z-mfm (sou f) (tar f) (m-negate (mat g))))
      (free-z-zero-mfm
       g))))

(defmethod add-cat-zerop ((x free-z-module))
  (zerop (rank x)))

(defmethod add-cat-zerop ((f csparsez-mfm))
  (with-slots (mat) f
    (if mat
	(m-zerop mat)
      (with-slots (snf) f
	(assert (not (null snf)) (f)
	  "Morphism was created with a null underlying matrix.")
	(zerop (rank snf))))))

(defmethod add-cat-zerop ((f free-z-zero-mfm))
  t)

(defmethod make-zero-obj ((x free-z-module))
  (make-free-z-module 0))

;;; The next four implementations have a certain elegance but don't
;;; build the csparsez's efficiently.

(defmethod direct-sum-projection-list ((sum free-z-module-direct-sum))
  "A list of the projections s<-sum, as s runs through sum's summands."
  (let ((n (rank sum))
	(r-accum 0)
	(ans '()))
    (dolist (s (summands sum) (nreverse ans))
      (let ((r (rank s)))
	(push (make-free-z-mfm sum s (make-zero-and-id r n 0 r-accum r #'make-sp-z))
	      ans)
	(incf r-accum r)))))

(defmethod direct-sum-inclusion-list ((sum free-z-module-direct-sum))
  "A list of the inclusions sum<-s, as s runs through sum's summands."
  (let ((m (rank sum))
	(r-accum 0)
	(ans '()))
    (dolist (s (summands sum) (nreverse ans))
      (let ((r (rank s)))
	(push (make-free-z-mfm s sum (make-zero-and-id m r r-accum 0 r #'make-sp-z))
	      ans)
	(incf r-accum r)))))

(defmethod mfm-from-direct-sum ((sum free-z-module-direct-sum) (tar0 free-z-module) mfm-list)
  (assert (every #'(lambda (f) (cat-equal-p (tar f) tar0)) mfm-list) ()
    "At least one element of mfm-list does not have target tar0.")
  (apply #'add (mapcar #'compose mfm-list (direct-sum-projection-list sum))))

(defmethod mfm-to-direct-sum ((sou0 free-z-module-direct-sum) (sum free-z-module) mfm-list)
  (assert (every #'(lambda (f) (cat-equal-p (sou f) sou0)) mfm-list) ()
    "At least one element of mfm-list does not have source sou0.")
  (apply #'add (mapcar #'compose (direct-sum-inclusion-list sum) mfm-list)))

;;; - - - - - - - - Methods for modules over a domain D - - - - - - - -

(defmethod rank ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (rank snf)))

(defmethod rank ((f free-z-zero-mfm))
  0)

(defmethod num-units ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (num-units snf)))

(defmethod num-units ((f free-z-zero-mfm))
  0)

(defmethod torsion ((f csparsez-mfm))
  (do-snf-if-nec f)
  (with-slots (snf) f
    (torsion snf)))

(defmethod torsion ((f free-z-zero-mfm))
  '())

(defgeneric image-contained-in-image (f g)
  (:documentation "Whether the image of f is contained in the image of g.
Here f and g are free-z-mfms.  They must have the same target."))

(defmethod image-contained-in-image :before ((f free-z-mfm) (g free-z-mfm))
  (assert (cat-equal-p (tar f) (tar g)) (f g) "The targets are not equal."))

(defmethod image-contained-in-image ((f csparsez-mfm) (g csparsez-mfm))
  (do-snf-if-nec g)
  (assert-has-p g)
  (m-image-contained-in-image (mat f) (slot-value g 'snf)))

(defmethod image-contained-in-image ((f free-z-mfm) (g free-z-zero-mfm))
  (add-cat-zerop f))

(defmethod image-contained-in-image ((f free-z-zero-mfm) (g free-z-mfm))
  t)

(defgeneric inverse-image (f g)
  (:documentation "The inverse image I under g of the image of f.
The two arguments must have the same target T, and f must be injective.
Returns I as an injective morphism into (sou g)."))

(defmethod inverse-image :before ((f free-z-mfm) (g free-z-mfm))
  (assert (cat-equal-p (tar f) (tar g)) (f g) "The targets are not equal.")
  (assert (monic-p f) (f) "The first argument is not injective."))

(defmethod inverse-image ((f csparsez-mfm) (g csparsez-mfm))
  (do-snf-if-nec g)
  (assert-has-p g)
  (assert-has-q g)
  (let ((ans (m-inverse-image (mat f) (slot-value g 'snf))))
    (make-free-z-mfm (make-free-z-module (m-num-cols ans)) (sou g) ans)))

(defmethod inverse-image ((f free-z-mfm) (g free-z-zero-mfm))
  (make-id-mfm (sou g)))

(defmethod inverse-image ((f free-z-zero-mfm) (g csparsez-mfm))
  (do-snf-if-nec g)
  (let ((kk (m-ker (slot-value g 'snf))))
    (make-free-z-mfm (make-free-z-module (m-num-cols kk)) (sou g) kk)))

;;; ----- Finitely-generated Z-modules, an abelian category. -----

(defclass z-module (abelian-cat-obj)
  ((inj :type free-z-mfm :initarg :inj :reader inj))
  (:documentation
   "A Z-module is implemented as an injective
morphism B `--> A of free-z-modules.  The 'actual' Z-module
is the quotient A/B.  The reader method 'inj' returns
the injective morphism."))
;; Normally inj should remember its mat and store the P's, but can
;; forget the Q's.  In other words, we'll normally call
;; allow-sou-coord-changes on inj right after it's created.

(defclass z-mfm (abelian-cat-mfm)
  ((lift :type free-z-mfm :initarg :lift :reader lift))
  (:documentation
   "A z-mfm from A/B to C/D is a free-z-mfm f from A to C.
It's required, but not always checked, that the image
of B under lift must be a subset of the image of D.
The reader method 'lift' returns f."))

(defclass z-module-direct-sum (z-module direct-sum)
  ()
  (:documentation "A direct sum of Z-modules."))

;;; --------------- Implementation of z-module/mfm ---------------

(defmethod integrity-check ((x z-module) &key (message ""))
  (integrity-check (inj x) :message message)
  (assert (monic-p (inj x)) (x)
    "In A/B, the internal map from B to A is not injective."))

(defmethod integrity-check ((f z-mfm) &key (message ""))
  (integrity-check (sou f) :message message)
  (integrity-check (tar f) :message message)
  (assert (image-contained-in-image (compose (lift f) (inj (sou f)))
				    (inj (tar f)))
      (f)
    "In A/B --> C/D, B does not map into D."))

;;; STOPPED HERE 10/26 9:13.

(defmethod cat-equal-p ((x z-module) (y z-module))
  "A strict definition: A/B and C/D are equal iff
A equals C, B equals D, and the injections are equal."
  (cat-equal-p (inj x) (inj y)))

(defmethod cat-equal-p ((f z-mfm) (g z-mfm))
  (add-cat-zerop (subtract f g)))

(defmethod compose ((f z-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (declare (type z-mfm g))
    (make-instance 'z-mfm
      :sou (sou g) :tar (tar f) :lift (compose (lift f) (lift g)))))

(defmethod make-id-mfm ((x z-module))
  (make-instance 'z-mfm
    :sou x :tar x :lift (make-id-mfm (tar (inj x)))))

(defmethod id-mfm-p ((f z-mfm))
  ;; :around checked sou = tar.
  (add-cat-zerop (subtract f (make-id-mfm (sou f)))))

(defmethod monic-p ((f z-mfm))
  (add-cat-zerop (ker f)))

(defmethod epic-p ((f z-mfm))
  (add-cat-zerop (coker f)))

(defmethod isomorphism-p ((f z-mfm))
  (and (monic-p f) (epic-p f)))

;; Need a method for make-inverse-mfm applied to a z-mfm.

(defmethod make-zero-obj ((x z-module))
  (let ((std-zero (make-zero-obj (sou (inj x))))) ;; = *free-z-zero-module*
    (make-instance 'z-module
      :sou std-zero :tar std-zero :inj (make-zero-mfm std-zero std-zero))))

(defmethod make-zero-mfm ((x z-module) (y z-module))
  (make-instance 'z-mfm
    :sou x :tar y :lift (make-zero-mfm (tar (inj x)) (tar (inj y)))))

(defmethod add-cat-zerop ((x z-module))
  (epic-p (inj x)))

(defmethod add-cat-zerop ((f z-mfm))
  (image-contained-in-image (lift f) (inj (tar f))))

(defmethod add ((f z-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (declare (type z-mfm g))
    (make-instance 'z-mfm
      :sou (sou f) :tar (tar f) :lift (add (lift f) (lift g)))))

(defmethod subtract ((f z-mfm) &rest more-fs)
  (let ((g (first more-fs)))
    (declare (type z-mfm g))
    (make-instance 'z-mfm
      :sou (sou f) :tar (tar f) :lift (subtract (lift f) (lift g)))))

(defmethod composition-zerop ((f z-mfm) (g z-mfm))
  "Only avoids creating the composition if the target is free."
  (if (add-cat-zerop (inj (tar f)))
      (composition-zerop (lift f) (lift g))
    (call-next-method)))

;; Need direct-sum stuff.  Introduce(?) a diagonal version of
;; mfm-(from|to)-direct-sum.  Then a z-module-direct-sum is the direct
;; sum of the summands' inj's, with source the free-z-mod-direct-sum
;; of the sou's, and ditto for target.

;;; STOPPED HERE 9/16 7:40

;;; Next: fix m-inverse-image in csparse.lisp.  Decide whether
;;; inverse-image for two csparsez-mfms needs assert-has-p,
;;; assert-has-q, or both.  Write ker in this file.  Write
;;; pullback-to-ker ("just backsolve every time"?)  Along the way,
;;; enforce monic-p for all inj fields in z-mfm's.  Write an
;;; integrity-check method for csparsez-mfm's, that checks the mat
;;; field if it is present, and checks the snf if it present without
;;; complaining if it's only partially filled out.

;;; ------------------------- Cochain Complexes -------------------------

(defclass ccx (add-cat-obj)
  ()
  (:documentation "A cochain complex [ccx] implements
ccx-term to return objects in some underlying additive
category, and implements ccx-diff, ccx-max-deg and
ccx-min-deg."))

(defgeneric ccx-term (cx i)
  (:documentation "Returns the degree-i term in the cochain complex cx."))

(defgeneric ccx-diff (cx i)
  (:documentation "Returns the differential d^i from term i to
term i+1 in the cochain complex cx.  The main requirement for a
cochain complex is, of course, that the composition of d^[i+1]
with d^i must be 0."))

(defgeneric ccx-max-deg (cx)
  (:documentation "This returns i to mean that all terms of
degree strictly greater than i in the cochain complex are zero.
Terms of degree leq i may or may not be zero."))

(defgeneric ccx-min-deg (cx)
  (:documentation "This returns i to mean that all terms of
degree strictly less than i in the cochain complex are zero.
Terms of degree geq i may or may not be zero."))

(defclass ccx-map (add-cat-mfm)
  ()
  (:documentation "A map of cochain complexes.  It must implement
ccx-map-term."))

(defgeneric ccx-map-term (map i)
  (:documentation "The morphism from the degree-i term
of the source to the degree-i term of the target.
The main requirement is that these maps commute with
the differentials."))

;;; ------- Implementation of ccx and ccx-map by hash-tables -------

(defclass hash-ccx (ccx)
  ((terms :type hash-table)
   (diffs :type hash-table)
   (zero-obj :type add-cat-obj
	     :documentation "Zero object for large or small i.")
   (min-deg :type integer :reader ccx-min-deg)
   (max-deg :type integer :reader ccx-max-deg))
  (:documentation "Default implementation of a cochain complex
using hash tables keyed on the degree i.  It's strongly recommended
that you use make-ccx to construct a hash-ccx."))

(defun make-ccx (terms diffs &optional (zero-obj nil))
  "Creates a hash-ccx.  terms is either nil or an eql
hash-table with the key i holding the i-th term.  diffs is
either nil or an eql hash-table with the key i holding
the i-th differential.  We use diffs to fill out missing
items in terms as necessary.  We always do an integrity
check for d d = 0.  zero-obj is the zero object
in the underlying category; if it's given as nil, the
function will try to supply the correct value."
  (unless terms (setq terms (make-hash-table)))
  (unless diffs (setq diffs (make-hash-table)))
  (maphash #'(lambda (i d-i)
	       (declare (integer i) (type add-cat-mfm d-i))
	       (multiple-value-bind (t-i has-t-i) (gethash i terms)
		 (declare (ignore t-i))
		 (unless has-t-i
		   (puthash i (sou d-i) terms)))
	       (multiple-value-bind (t-i1 has-t-i1) (gethash (1+ i) terms)
		 (declare (ignore t-i1))
		 (unless has-t-i1
		   (puthash (1+ i) (tar d-i) terms)))
	       (multiple-value-bind (d-i1 has-d-i1) (gethash (1+ i) diffs)
		 (when has-d-i1
		   (assert (composition-zerop d-i1 d-i) ()
		     "Violates d d = 0 in degrees ~D <- ~D <- ~D."
		     (+ i 2) (+ i 1) i))))
	   diffs)
  (unless zero-obj
    (block guess-zero
      (with-hash-table-iterator (next-term terms)
	(multiple-value-bind (has-i i term) (next-term)
	  (declare (ignore i) (type add-cat-obj term))
	  (when has-i
	    (setq zero-obj (make-zero-obj term))
	    (return-from guess-zero nil)))))
    (assert zero-obj (zero-obj)
      "Couldn't identify the zero object in the underlying category."))
  (let ((min-deg nil)
	(max-deg nil))
    (maphash #'(lambda (i term)
		 (declare (integer i) (type add-cat-obj term))
		 (unless (add-cat-zerop term)
		   (setq min-deg (if min-deg (min min-deg i) i))
		   (setq max-deg (if max-deg (max max-deg i) i))))
	     terms)
    (unless min-deg (setq min-deg 0))
    (unless max-deg (setq max-deg (1- min-deg)))
    (let ((ans (make-instance 'hash-ccx)))
      (setf (slot-value ans 'terms) terms)
      (setf (slot-value ans 'diffs) diffs)
      (setf (slot-value ans 'zero-obj) zero-obj)
      (setf (slot-value ans 'min-deg) min-deg)
      (setf (slot-value ans 'max-deg) max-deg)
      ans)))      

(defmethod ccx-term ((x hash-ccx) i)
  (with-slots (terms) x
    (declare (hash-table terms))
    (multiple-value-bind (term has-term) (gethash i terms)
      (if has-term
	  term
	(slot-value x 'zero-obj)))))

(defmethod ccx-diff ((x hash-ccx) i)
  (with-slots (diffs) x
    (declare (hash-table diffs))
    (multiple-value-bind (d has-d) (gethash i diffs)
      (if has-d
	  d
	(make-zero-mfm (ccx-term x i) (ccx-term x (1+ i)))))))

;;; --------- Implementation of ccx as an additive category ---------

(defmethod cat-equal-p ((x ccx) (y ccx))
  (do ((i (min (ccx-min-deg x) (ccx-min-deg y)) (1+ i))
       (i-max (max (ccx-max-deg x) (ccx-max-deg y))))
      ((> i i-max) t)
    (unless (cat-equal-p (ccx-diff x i) (ccx-diff y i))
      (return nil))))

(defmethod cat-equal-p ((f ccx-map) (g ccx-map))
  (and (cat-equal-p (sou f) (sou g))
       (cat-equal-p (tar f) (tar g))
       (do ((i (min (ccx-min-deg (sou f)) (ccx-min-deg (tar f))) (1+ i))
	    (i-max (max (ccx-max-deg (sou f)) (ccx-max-deg (tar f)))))
	   ((> i i-max) t)
	 (unless (cat-equal-p (ccx-map-term f i) (ccx-map-term g i))
	   (return nil)))))

;;; Need to finish implementing add-cat methods for ccx and ccx-map.

;;; ----- Version of cohomology until we have torsion Z-modules -----

(defmethod betti-numbers ((cx ccx) (i integer))
  "Assumes cx is a complex of free-z-modules and mfms.  Returns
two values: the i-th Betti number, and a list of the torsion
coefficients."
  (let ((di (ccx-diff cx i))
	(dj (ccx-diff cx (1- i)))) ;; j means i-1
    (declare (type free-z-mfm di dj))
    (labels ((make-csparsez-zero-mfm (so ta) ;; stupid and temporary!
	       (make-instance 'csparsez-mfm
		 :sou so :tar ta
		 :mat (make-csparse-zero (rank ta) (rank so)))))
      (when (typep di 'free-z-zero-mfm)
	(setq di (make-csparsez-zero-mfm (sou di) (tar di))))
      (when (typep dj 'free-z-zero-mfm)
	(setq dj (make-csparsez-zero-mfm (sou dj) (tar dj)))))
    (do-snf-if-nec di)
    (let* ((snfi (slot-value di 'snf))
	   (kerreti (m-ker-retraction snfi))
	   (f (m-mult kerreti (mat dj)))
	   (snff (make-snf f t nil t)))
      (declare (type snf snfi snff) (type csparse kerreti f))
      (values (- (m-num-rows kerreti) (rank snff))
	      (mapcar #'abs (mapcar #'sp-integer-value (torsion snff)))))))
    
;;; ------------------------- Tensor -------------------------

(defclass tensor-obj ()
  ((factor1 :reader factor1 :initarg :factor1)
   (factor2 :reader factor2 :initarg :factor2)))

(defclass tensor-free-z-module (tensor-obj free-z-module)
  ()
  (:documentation "The tensor product, over Z, of two free
Z-modules."))

(defmethod make-tensor-free-z-module ((fac1 free-z-module) (fac2 free-z-module))
  (make-instance 'tensor-free-z-module
    :rank (* (rank fac1) (rank fac2)) :factor1 fac1 :factor2 fac2))

(defgeneric make-tensor-morphism (f g so ta)
  (:documentation
"The arguments are f g so ta.  Here f and g are morphisms.
Output is the induced morphism from (sou f)-tensor-(sou g)
to (tar f)-tensor-(tar g).  The latter two tensor-product spaces must be
provided as the arguments so and ta."))   

(defmethod make-tensor-morphism :before ((f free-z-mfm) (g free-z-mfm) (so tensor-free-z-module) (ta tensor-free-z-module))
  (assert (and (cat-equal-p (sou f) (factor1 so))
	       (cat-equal-p (sou g) (factor2 so))) ()
    "The third argument is not the tensor product of the sources of the
first and second arguments.")
  (assert (and (cat-equal-p (tar f) (factor1 ta))
	       (cat-equal-p (tar g) (factor2 ta))) ()
    "The fourth argument is not the tensor product of the targets of the
first and second arguments."))

(defmethod make-tensor-morphism ((f csparsez-mfm) (g csparsez-mfm) (so tensor-free-z-module) (ta tensor-free-z-module))
  (let* ((ans (make-csparse-zero (rank ta) (rank so))))
    (declare (type csparse ans))
    (with-csparse-slots ((cols-ans cols)) ans
      (with-csparse-slots ((n1 n) (cols1 cols)) (mat f)
        (with-csparse-slots ((m2 m) (n2 n) (cols2 cols)) (mat g)
	  (dotimes-f (j1 n1)
	    (let ((j1n2 (* j1 n2)))
	      (declare (fixnum j1n2))
	      (dolist (e1 (svref cols1 j1))
		(let* ((i1 (sp-i e1))
		       (i1m2 (* i1 m2)))
		  (declare (fixnum i1 i1m2))
		  (dotimes-f (j2 n2)
		    (dolist (e2 (svref cols2 j2))
		      (let ((i2 (sp-i e2)))
			(declare (fixnum i2))
			(push (sp-mult e1 e2 (+ i1m2 i2))
			      (svref cols-ans (+ j1n2 j2))))))))))))
      (dotimes-f (j (m-num-cols ans))
	(setf (svref cols-ans j) (nreverse (svref cols-ans j))))
      (make-free-z-mfm so ta ans))))

(defmethod make-tensor-morphism ((f free-z-mfm) (g csparsez-mfm) (so tensor-free-z-module) (ta tensor-free-z-module))
  (make-zero-mfm so ta))

(defmethod make-tensor-morphism ((f csparsez-mfm) (g free-z-mfm) (so tensor-free-z-module) (ta tensor-free-z-module))
  (make-zero-mfm so ta))

