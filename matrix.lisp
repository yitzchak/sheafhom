(in-package shh2)

(declaim (optimize speed))

;;; A matrix is an instance of one of these classes: csparse, snf,
;;; elementary matrices (perm2, perm, transv), dense-matrix-mod-p,
;;; two-dimensional arrays such as dense-matrix-z, and perhaps more as
;;; the code evolves.  A matrix class is not required to implement all
;;; the methods here.

(defgeneric m-num-rows (A)
  (:documentation "Returns the number of rows in the matrix A."))

(defgeneric m-num-cols (A)
  (:documentation "Returns the number of columns in the matrix A."))

(defgeneric m-zerop (A)
  (:documentation "Returns true if and only if A is the zero matrix."))

(defgeneric m-id-p (A)
  (:documentation "Returns true if and only if A is the identity matrix."))

(defgeneric m-add (A B)
  (:documentation
   "Returns the matrix sum A + B.  Check the defmethods for details."))

(defgeneric m-subtract (A B)
  (:documentation
   "Returns the matrix difference A - B.  Check the defmethods for details."))

(defgeneric m-negate (A)
  (:documentation
   "Returns the matrix negative -A.  Check the defmethods for details."))

(defgeneric m-mult (A B)
  (:documentation
   "Returns the matrix product A * B.  Check the defmethods for details."))

(defgeneric m-product-zerop (A B)
  (:documentation
   "Returns true if and only if the matrix product A * B is zero,
but does not compute and store the product."))

(defgeneric m-transpose (A)
  (:documentation
   "Returns the transpose of the matrix A.  Check the defmethods
for details."))

(defgeneric m-inverse (A)
  (:documentation
"Returns the inverse of the matrix A, assuming it exists."))

(defgeneric m-inverse-transpose (A)
  (:documentation
"Returns the inverse-transpose of the matrix A, assuming it exists."))

(defgeneric m-translate (A incr)
  (:documentation
"Returns a new matrix with incr added to all the row and column indices."))

(defgeneric m-ker (A &optional make-sp)
  (:documentation
   "Returns a matrix whose columns are a D-basis for the kernel of A.
Check the defmethods for details."))

(defgeneric mat (x)
  (:documentation
   "If an object x has an underlying matrix in some appropriate sense,
this method returns the matrix.  If x itself is a matrix, we return it
directly.  Check the defmethods for details."))

;;; ----- Implementation for array types of dimension two -----

(defmethod m-num-rows ((A array))
  "For an m-by-n array, returns m."
  (if (= (array-rank A) 2)
      (array-dimension A 0)
    (call-next-method)))

(defmethod m-num-cols ((A array))
  "For an m-by-n array, returns n."
  (if (= (array-rank A) 2)
      (array-dimension A 1)
    (call-next-method)))

(defmethod mat ((A array))
  "For an m-by-n array, returns A itself."
  (if (= (array-rank A) 2)
      A
    (call-next-method)))

;;; ---------- Other general implementations ----------

(defmethod m-inverse-transpose ((A t))
  "Default implementation: (m-inverse (m-transpose A))."
  (m-inverse (m-transpose A)))

