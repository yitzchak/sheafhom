(in-package shh2)

(declaim (optimize safety debug)) ;; for now

;;; ------------------------------------------------------------

(defgeneric action (g x)
  (:documentation
   "If g is a group-elt and x an object in a category, this returns
an automorphism of x, so that the whole thing is a left action of
a group on x.  That is, (action (mult g h) x) must be
the same as (compose (action g x) (action h x))."))

;;; ------------------------------------------------------------

(defclass z-gg (free-z-module)
  ((gg :initarg :gg :type group :documentation "The underlying group.")
   (g-vec :initarg :g-vec :type simple-vector
	  :documentation "Maps code number i to g.")
   (g-to-i :initarg :g-to-i :type hash-table
	   :documentation "Maps (hash-key g) to code number i."))
  (:documentation "The group ring ZG for a finite group gg = G."))

(defun make-z-gg (gg)
  (let ((n (order gg)))
    (let ((g-vec (make-array n))
	  (g-to-i (make-hash-table :test #'equalp :size n))
	  (i 0))
      (declare (fixnum i))
      (do-mset (g gg)
	(setf (svref g-vec i) g)
	(puthash (hash-key g) i g-to-i)
	(incf i))
      (make-instance 'z-gg :gg gg :g-vec g-vec :g-to-i g-to-i))))

(defmethod action ((g group-elt) (x z-gg))
  (with-slots (gg g-vec g-to-i) x
    (assert (mset-member g gg) () "g is not in the underlying group.")
    (let ((n (order gg)))
      (let ((ans (make-csparse-zero n n)))
	(dotimes-f (j n)
	  (let* ((h (svref g-vec j))
		 (gh (mult g h))
		 (i (gethash (hash-key gh) g-to-i)))
	    (csparse-set ans (make-sp-z i 1) j)))
	(make-free-z-mfm x x ans)))))

;;; ------------------------------------------------------------

(defmethod action ((g group-elt) (tt tensor-obj))
  "The diagonal action on a tensor product."
  (make-tensor-morphism (action g (factor1 tt)) (action g (factor2 tt)) tt tt))

(defmethod coinvariants ((gg group) (x free-z-module))
  "Provisional version.  Let f be the direct sum of maps (I-g) to x
as g runs through a set of generators of gg.  We return f.  The
coinvariants are the cokernel of f.  See m-coker in csparse.lisp,
though the coinvariants also have to take torsion into account.
See also m-coker-section."
  (let ((gs (generators gg)))
    (if (endp gs)
	(call-next-method)
      (let* ((id-x (make-id-mfm x))
	     (mfm-list (mapcar #'(lambda (g) (subtract (action g x) id-x)) gs))
	     (summands (mapcar #'sou mfm-list)) ;; (x x ... x)
	     (sum (make-free-z-module-direct-sum summands))
	     (f (destroy-matrix
		 (allow-sou-coord-changes
		  (mfm-from-direct-sum sum x mfm-list)))))
	f))))

