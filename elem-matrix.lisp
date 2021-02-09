(in-package shh2)

(declaim (optimize speed))

(defstruct (perm2 (:constructor make-perm2 (i1 i2)) (:copier nil))
  "A permutation matrix: the identity, but with columns i1 and i2 swapped.
We require i1 /= i2."
  ;; [7/31/07] i1 == i2 may slip in in permute-rows-onto-diag.  I don't
  ;; think it's causing bona fide errors.
  i1 i2)

(defmacro with-perm2-slots (var &body body)
  `(let ((i1 (perm2-i1 ,var))
         (i2 (perm2-i2 ,var)))
     (declare (type nnfixnum i1 i2))
     ,@body))

(defmethod print-object ((e perm2) stream)
  (with-perm2-slots e
    (format stream "(:P ~D ~D)" i1 i2)))

(defmethod m-transpose ((e perm2))
  e)

(defmethod m-inverse ((e perm2))
  e)

(defmethod m-inverse-transpose ((e perm2))
  e)

(defun perm2-times-vector (e w)
  "Modifies the simple-vector w by swapping entries i1 and i2."
  (declare (type perm2 e) (simple-vector w))
  (with-perm2-slots e
    (psetf (svref w i1) (svref w i2)
	   (svref w i2) (svref w i1))))

(defmethod m-translate ((e perm2) incr)
  (declare (fixnum incr))
  (with-perm2-slots e
    (make-perm2 (+ i1 incr) (+ i2 incr))))

(defmethod integrity-check ((e perm2) &key (message "") n)
  "Checks whether e is a valid n-by-n permutation matrix."
  (with-perm2-slots e
    (assert (<= 0 i1) (e) "~AOut of bounds." message)
    (assert (<= 0 i2) (e) "~AOut of bounds." message)
    (when n
      (assert (< i1 n) (e) "~AOut of bounds." message)
      (assert (< i2 n) (e) "~AOut of bounds." message))
    (assert (/= i1 i2) (e) "~Aperm2 should have ~D /= ~D"
	    message i1 i2)))

(defmethod mat ((a perm2))
  "Just returns a."
  a)

(defmethod m-zerop ((a perm2))
  nil)

(defmethod m-id-p ((a perm2))
  (with-perm2-slots a
    (= i1 i2))) ;; i1 /= i2 is "required", but just in case...

(defmethod m-product-zerop ((A perm2) B)
  (m-zerop B))

(defmethod m-product-zerop (A (B perm2))
  (m-zerop A))

;;; ----------

(defstruct (perm (:constructor make-perm (arr)) (:copier nil))
  "A general n-by-n permutation matrix.  arr is a simple-vector of
length n holding a permutation of {0,...,n-1}.  The permutation
is a function j -> i given by the rule i = (svref arr j).  As
a matrix, the perm has a 1 in the i,j entry for all j, and 0
elsewhere.
  If scr is non-null, it is a simple-vector of length n that
internal methods use for scratchwork.  The code will create and
destroy it automatically."
  arr
  (scr nil))

(defun make-id-perm (n)
  "Constructs an n-by-n permutation, initialized with the identity."
  (assert (typep n 'nnfixnum) () "Argument ~A must be a fixnum >= 0." n)
  (let ((arr (make-array n)))
    (declare (simple-vector arr))
    (dotimes-f (j n)
      (setf (svref arr j) j))
    (make-perm arr)))

(defmacro with-perm-slots (var &body body)
  `(let ((arr (perm-arr ,var)))
     (declare (simple-vector arr))
     (let ((n (length arr)))
       (declare (type nnfixnum n))
       ,@body)))

(defun get-perm-scr (e)
  "Returns the n-vector in the scr slot of the perm 'e', creating
and caching it beforehand if necessary."
  (aif (perm-scr e)
       it
    (with-perm-slots e
      (setf (perm-scr e) (make-array n)))))

(defmethod print-object ((e perm) stream)
  (format stream "(:PN ~S)" (perm-arr e)))

(defmethod m-num-rows ((e perm))
  (with-perm-slots e
    n))

(defmethod m-num-cols ((e perm))
  (with-perm-slots e
    n))

(defmethod m-transpose ((e perm))
  (m-inverse e))

(defmethod m-inverse ((e perm))
  (with-perm-slots e
    (let ((inv (make-array n)))
      (dotimes-f (j n)
	(setf (svref inv (the nnfixnum (svref arr j))) j))
      (make-perm inv))))

(defmethod m-inverse-transpose ((e perm))
  e)

(defun perm-times-vector (e w)
  "Modifies the simple-vector w by permuting its entries, yielding e*w."
  (declare (type perm e) (simple-vector w))
  (with-perm-slots e
    (let ((scr (get-perm-scr e)))
      (declare (simple-vector scr))
      (dotimes-f (j n)
	(setf (svref scr (the nnfixnum (svref arr j))) (svref w j)))
      (dotimes-f (j n)
	(setf (svref w j) (svref scr j))))))

(defun perm-times-sparse-v (P a)
  "Returns the sparse-v P*a, freshly allocated.  Does not alter a."
  (let ((arr (perm-arr P))
	(ans '()))
    (declare (simple-vector arr))
    (dolist (e a)
      (push (copy-sp e (svref arr (sp-i e))) ans))
    (sort ans #'(lambda (e1 e2) (< (sp-i e1) (sp-i e2))))))

(defmethod m-mult ((a perm) (j integer))
  "Viewing a perm as a function [0,n) -> [0,n), this method returns
the image of j under that function."
  (svref (the simple-vector (perm-arr a)) j))

(defmethod m-mult ((a perm) (b perm))
  "Modifies a in place to hold the product a*b."
  (with-perm-slots a
    (let ((arr-b (perm-arr b)))
      (declare (simple-vector arr-b))
      (assert (= n (length arr-b)) (a b)
	"Dim mismatch: multiplying size ~D by size ~D." n (length arr-b))
      (let ((prod (get-perm-scr a)))
	(declare (simple-vector prod))
	(dotimes-f (j n)
	  (setf (svref prod j) (svref arr (the nnfixnum (svref arr-b j)))))
	(dotimes-f (j n)
	  (setf (svref arr j) (svref prod j)))
	a))))

(defmethod m-mult ((a perm) (b perm2))
  "Modifies a in place to hold the product a*b."
  (with-perm2-slots b
    (perm-swap-cols a i1 i2)))

(defun perm-swap-cols (a i1 i2)
  "Modifies the perm 'a' in place, permuting the two indicated columns."
  (let ((arr (perm-arr a)))
    (declare (simple-vector arr))
    (psetf (svref arr i1) (svref arr i2)
	   (svref arr i2) (svref arr i1))
    a))

(defmethod m-mult ((a perm2) (b perm))
  "Modifies b in place to hold the product a*b."
  (with-perm2-slots a
    (unless (= i1 i2)
      (with-perm-slots b
	(let ((count 0))
	  (declare (fixnum count))
	  (dotimes-f (j n)
	    (cond ((= i1 (the nnfixnum (svref arr j)))
		   (setf (svref arr j) i2)
		   (incf count)
		   (when (= count 2)
		     (return)))
		  ((= i2 (the nnfixnum (svref arr j)))
		   (setf (svref arr j) i1)
		   (incf count)
		   (when (= count 2)
		     (return))))))))
    a))

(defmethod m-translate ((e perm) incr)
  (with-perm-slots e
    (let ((y (make-array (+ n incr))))
      (declare (simple-vector y))
      (dotimes-f (j incr)
	(setf (svref y j) j))
      (dotimes-f (j n)
        (setf (svref y (+ j incr)) (+ (the nnfixnum (svref arr j)) incr)))
      (make-perm y))))

(defmethod integrity-check ((e perm) &key (message "") n0)
  "Checks whether e is a valid n0-by-n0 permutation matrix."
  (with-perm-slots e
    (when n0
      (assert (= n n0) (e)
	"~ASize ~D, expected ~D." message n n0))
    (let ((scr (get-perm-scr e)))
      (declare (simple-vector scr))
      (fill scr nil)
      (dotimes-f (j n)
	(let ((i (svref arr j)))
	  (declare (type nnfixnum i))
	  (assert (<= 0 i) (e)
	    "~ANegative i = ~D in image at j = ~D." message i j)
	  (assert (< i n) (e)
	    "~Ai = ~D >= n := ~D in image at j = ~D." message i n j)
	  (assert (not (svref scr i)) (e)
	    "~Ai = ~D occurred twice in image, the 2nd time at j = ~D." message i j)
	  (setf (svref scr i) t)))
      (dotimes-f (i n)
	(assert (svref scr i) (e)
	  "~Ai = ~D never occurred in image." message i)))))
    
(defmethod mat ((e perm))
  "Just returns e."
  e)

(defmethod m-zerop ((e perm))
  nil)

(defmethod m-id-p ((e perm))
  (with-perm-slots e
    (dotimes-f (j n t)
      (unless (= (the nnfixnum (svref arr j)) j)
	(return nil)))))

(defmethod m-product-zerop ((A perm) B)
  (m-zerop B))

(defmethod m-product-zerop (A (B perm))
  (m-zerop A))

;;; ----------

(defstruct (transv (:constructor make-transv (j i-and-v)) (:copier nil))
  "A transvection matrix: the identity, with an extra entry of
value v at i,j.  i-and-v is a sparse-elt holding i and v.
We require i /= j."
  j i-and-v)

(defmacro with-transv-slots (var &body body)
  `(let ((j (transv-j ,var))
         (i-and-v (transv-i-and-v ,var)))
     (declare (type nnfixnum j))
     ,@body))

(defmacro with-transv-slot-i (var &body body)
  `(let ((i (sp-i-func (transv-i-and-v ,var))))
     (declare (type nnfixnum i))
     ,@body))

(defmethod print-object ((e transv) stream)
  (with-transv-slots e
    (format stream "(:T ~D ~S)" j i-and-v)))

(defmethod m-transpose ((e transv))
  (with-transv-slots e
    (with-transv-slot-i e
      (make-transv i (copy-sp i-and-v j)))))

(defmethod m-inverse ((e transv))
  (with-transv-slots e
    (make-transv j (sp-negate i-and-v))))

(defmethod m-inverse-transpose ((e transv))
  (with-transv-slots e
    (with-transv-slot-i e
      (make-transv i (sp-negate i-and-v j)))))

(defun transv-times-vector (e w)
  "Modifies the simple-vector w by adding v times entry j to entry i.
The entries of w must be integers, representing elements of either Z
or Z/p.  The ring has to be the same one used by i-and-v."
  (declare (type transv e) (simple-vector w))
  (let ((p nil))
    (with-transv-slots e
      (aif (sp-f_p-p i-and-v)
	   (setq p it)
	(unless (sp-z-p i-and-v)
	  (error "This method is only for D = Z and quotients of Z.")))
      (with-transv-slot-i e
	(let ((ans (+ (the integer (svref w i))
		      (* (the integer (sp-integer-lift i-and-v))
			 (the integer (svref w j))))))
	  (declare (integer ans))
	  (setf (svref w i)
	    (if p
		(rem ans p) ;; use mod at end, but rem here is ok and faster
	      ans)))))))

(defmethod m-translate ((e transv) incr)
  (declare (fixnum incr))
  (with-transv-slots e
    (with-transv-slot-i e
      (make-transv (+ j incr) (copy-sp i-and-v (+ i incr))))))

(defmethod integrity-check ((e transv) &key (message "") n)
  "Checks whether e is a valid n-by-n transvection matrix."
  (with-transv-slots e
    (with-transv-slot-i e
      (assert (<= 0 i) (e) "~AOut of bounds." message)
      (assert (<= 0 j) (e) "~AOut of bounds." message)
      (when n
	(assert (< i n) (e) "~AOut of bounds." message)
	(assert (< j n) (e) "~AOut of bounds." message))
      (assert (/= i j) (e) "~Atransv should have ~D /= ~D"
	      message i j)
      (assert (not (sp-zerop i-and-v)) ()
	"~Atransv needs non-zero value." message))))

(defmethod mat ((a transv))
  "Just returns a."
  a)

(defmethod m-zerop ((a transv))
  nil)

(defmethod m-id-p ((a transv))
  nil)

(defmethod m-product-zerop ((A transv) B)
  (m-zerop B))

(defmethod m-product-zerop (A (B transv))
  (m-zerop A))

;;; ----------

;;; In the future, may need dilation (dilatation) matrices that are
;;; the identity except for a unit at a single position on the diagonal.

;;; ----------

(defun elem-times-vector (e w)
  (etypecase e
    (perm2 (perm2-times-vector e w))
    (perm (perm-times-vector e w))
    (transv (transv-times-vector e w))))

;;; -------------------- Unit tests for perm --------------------

(let ((p-023-14 (make-id-perm 5)))
  (with-perm-slots p-023-14 ;; (0 2 3)(1 4) in cycle notation
    (declare (ignore n))
    (setf (svref arr 0) 2
	  (svref arr 2) 3
	  (svref arr 3) 0)
    (setf (svref arr 1) 4
	  (svref arr 4) 1))
  (integrity-check p-023-14 :n0 5)
  (let ((x (make-id-perm 5))
	(i 0))
    (dotimes-f (j 7)
      (let ((zero-mod-6 (zerop (mod i 6))))
	(assert (if (m-id-p x) zero-mod-6 (not zero-mod-6)) ()))
      (m-mult x p-023-14)
      (integrity-check x :n0 5)
      (incf i)))
  (let ((w (make-array 5 :initial-contents '(10 11 12 13 14))))
    (perm-times-vector p-023-14 w)
    (assert (equalp w (make-array 5 :initial-contents '(13 14 10 12 11))) ())
    (perm-times-vector (m-inverse p-023-14) w)
    (assert (equalp w (make-array 5 :initial-contents '(10 11 12 13 14))) ()))
#|
  (let ((w (list '(0 . 10) '(1 . 11) '(2 . 12) '(3 . 13) '(4 . 14))))
    (setq w (perm-times-sparse-v p-023-14 w))
    (assert (equalp w (list '(0 . 13) '(1 . 14) '(2 . 10) '(3 . 12) '(4 . 11))) ())
    (setq w (perm-times-sparse-v (m-inverse p-023-14) w))
    (assert (equalp w (list '(0 . 10) '(1 . 11) '(2 . 12) '(3 . 13) '(4 . 14))) ()))
|#
  (m-mult p-023-14 (make-perm2 0 1)) ;; make it (0 4 1 2 3)
  (integrity-check p-023-14 :n0 5)
  (with-perm-slots p-023-14
    (declare (ignore n))
    (assert (and (= (svref arr 0) 4)
		 (= (svref arr 4) 1)
		 (= (svref arr 1) 2)
		 (= (svref arr 2) 3)
		 (= (svref arr 3) 0)) ()))
  (m-mult p-023-14 (make-perm2 0 1)) ;; put it back to (0 2 3)(1 4)
  (integrity-check p-023-14 :n0 5)
  (m-mult (make-perm2 0 1) p-023-14) ;; make it (0 2 3 1 4)
  (integrity-check p-023-14 :n0 5)
  (with-perm-slots p-023-14
    (declare (ignore n))
    (assert (and (= (svref arr 0) 2)
		 (= (svref arr 2) 3)
		 (= (svref arr 3) 1)
		 (= (svref arr 1) 4)
		 (= (svref arr 4) 0)) ()))
  (m-mult (make-perm2 0 1) p-023-14) ;; put it back to (0 2 3)(1 4)
  (integrity-check p-023-14 :n0 5))
