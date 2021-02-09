(in-package shh2)

(declaim (optimize safety debug)) ;; for now

;;; -------------------- Categories --------------------

;;; The cat code is dedicated to Kat Zhang on her 17th birthday.

(defclass cat-obj ()
  ()
  (:documentation "An object in a category."))

(defclass cat-mfm ()
  ((sou :type cat-obj :reader sou :initarg :sou
	:documentation "The source object.")
   (tar :type cat-obj :reader tar :initarg :tar
	:documentation "The target object."))
  (:documentation "A morphism tar <--- sou in a category."))  

(defgeneric cat-equal-p (x y)
  (:documentation "Whether two objects or morphisms are equal.
For morphisms, this includes (by definition) checking whether
the sources and targets are equal."))

(defgeneric compose (f &rest more-fs)
  (:documentation "Returns the composition
   <--f-- <--g-- <--h-- ...
where more-fs is the list (g h ...).  Each primary method
for compose should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments.  The :before method checks whether
inner objects match."))

(defgeneric make-id-mfm (obj)
  (:documentation "Returns the identity morphism from obj to itself."))

(defgeneric id-mfm-p (f)
  (:documentation "Whether f is an identity morphism."))

(defgeneric monic-p (f)
  (:documentation "Whether f is a monomorphism."))

(defgeneric epic-p (f)
  (:documentation "Whether f is a epimorphism."))

(defgeneric isomorphism-p (f)
  (:documentation "Whether f is an isomorphism."))

(defgeneric make-inverse-mfm (f)
  (:documentation "Returns the inverse morphism of f.  If f is
not an isomorphism, the result is unspecified."))

;;; - - - - - - - - - - Partial Implementations - - - - - - - - - - -

(defmethod compose :around ((f cat-mfm) &rest more-fs)
  "Each primary method for compose should assume more-fs has exactly
one element, because the :around method will handle other
numbers of arguments."
  (if (endp more-fs)
      f
    (if (endp (rest more-fs))
	(call-next-method f more-fs)
      (let ((fg (call-next-method f (list (first more-fs)))))
	(apply #'compose (cons fg (rest more-fs)))))))

(defmethod compose :before ((f cat-mfm) &rest more-fs)
  "Checks first whether the inner objects match."
  (let ((g (first more-fs)))
    (assert (cat-equal-p (sou f) (tar g)) (f g)
      "Objects in the middle of the composition are unequal.")))

(defmethod id-mfm-p :around ((f cat-mfm))
  "Checks first whether source and target are equal."
  (and (cat-equal-p (sou f) (tar f))
       (call-next-method)))

