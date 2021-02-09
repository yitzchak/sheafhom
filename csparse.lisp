(in-package shh2)

(declaim (optimize speed))

;;; Sparse linear algebra for morphisms of D-modules, where D is an
;;; integral domain.

;;; Since our main engine is Smith normal form, and this is only
;;; defined over a principal ideal domain, we are pretty much
;;; committing to such a D.  But check Cohen, vol II, because he seems
;;; to define HNF, at least, over arbitrary Dedekind domains.

;;; As of Sheafhom 2.2 (August 2006), the implementations still rely
;;; on D being Euclidean.  The code is divided into three main
;;; sections by lines of =====.  The first section is for arbitrary
;;; domains, the second for Euclidean domains, the third for the
;;; fields F_p, and the fourth for Z only.

;;; The end of the four main sections of code is marked with a line
;;; of #####.  After that come unit tests, as well as some old,
;;; commented-out code that we keep around for reference.

;;; Immediate parent: Sheafhom II (Sheafhom 2.0), Java, 2003-2004.
;;; Grandparent: Sheafhom, Lisp, 1993-1999.
;;; These are at http://www.geocities.com/mmcconnell17704/math.html
;;; Earlier: various Lisp programs starting from 1986.
;;; "Book of J" source: APL code for jac from the early 1980s,
;;; first used for a published paper at Epiphany 1985.

(defstruct (csparse
            ;; Constructors: make-csparse, (easier) make-csparse-zero
            (:copier nil)) ;; see csparse-copy
  "A csparse is a sparse m-by-n matrix over the integral domain D.
Here m and n must be fixnums [single-precision integers] and must be
non-negative.  cols is an array of length n.  The j-th column of the
matrix is a sparse-v held in the j-th entry of cols.  The slots rlen
and clen are arrays, of lengths m and n, respectively.  The i-th entry
of rlen is -1 plus the number of non-zeroes in the i-th row of the
matrix.  The j-th entry of clen is -1 plus the number of non-zeroes in
the j-th column.
  Note: two csparse's are mathematically equal iff they are equalp."
  m n cols rlen clen)

(defun make-csparse-zero (m n)
  "Constructs an m-by-n csparse with all entries initialized to zero."
  (assert (typep m 'nnfixnum) (m)
    "The row dimension ~D should be a non-negative fixnum." m)
  (assert (typep n 'nnfixnum) (n)
    "The column dimension ~D should be a non-negative fixnum." n)
  (make-csparse :m m :n n
		:cols (make-array n :initial-element '())
		:rlen (make-array m :initial-element -1)
		:clen (make-array n :initial-element -1)))

(defmacro with-csparse-slots (slots var &body body)
  "Version of with-slots for csparse, including type declarations.
Does not support setf."
  (if (endp slots)
      `(progn ,@body)
    (if (atom (first slots))
        `(with-csparse-slots
             ,(cons (list (first slots) (first slots)) (rest slots))
           ,var ,@body)
      (let ((var-name (first (first slots)))
            (slot-name (second (first slots)))
            accessor type)
        (ecase slot-name
          (m (setq accessor 'csparse-m type 'nnfixnum))
          (n (setq accessor 'csparse-n type 'nnfixnum))
          (cols (setq accessor 'csparse-cols type 'simple-vector))
	  (rlen (setq accessor 'csparse-rlen type 'simple-vector))
	  (clen (setq accessor 'csparse-clen type 'simple-vector)))
        `(let ((,var-name (,accessor (the csparse ,var))))
           (declare (type ,type ,var-name))
           (with-csparse-slots ,(rest slots) ,var ,@body))))))

(defun reset-markowitz (A &optional (rl (csparse-rlen A)) (cl (csparse-clen A)))
  "Overwrites rl and cl to reflect the current contents of A's cols.
By default, these are the rlen and clen fields of A itself.  To know
what they are overwritten with, see the documentation on rlen and clen
in csparse.  Returns A."
  (declare (simple-vector rl cl))
  (with-csparse-slots (m n cols) A
    (assert (= m (length rl)) () "rl has wrong length.")
    (assert (= n (length cl)) () "cl has wrong length.")
    (fill rl -1)
    (fill cl -1)
    (dotimes-f (j n A)
      (dolist (e (the sparse-v (svref cols j)))
	(incf (svref rl (sp-i e)))
	(incf (svref cl j))))))

(defun test-markowitz (A &key (message ""))
  "An integrity check: whether rlen, clen match m, n, cols."
  (with-csparse-slots (m n rlen clen) A
    (let ((rl (make-array m))
	  (cl (make-array n)))
      (reset-markowitz A rl cl)
      (assert (equalp rl rlen) ()
	"~AMarkowitz row count is off." message)
      (assert (equalp cl clen) ()
	"~AMarkowitz column count is off." message))))

(defun input-csparse (m n entries &optional (make-sp #'make-sp-z))
  "Returns an m-by-n csparse whose entries run through the proper list
'entries' in row-major order.  If the list is too short, we reread
it cyclically, in the spirit of APL's ravel function (rho).  make-sp
plays the same role as in input-sparse-v (q.v.)."
  (assert (typep m 'nnfixnum) (m)
    "The row dimension ~D should be a non-negative fixnum." m)
  (assert (typep n 'nnfixnum) (n)
    "The column dimension ~D should be a non-negative fixnum." n)
  (assert (not (endp entries)) (entries) "List of entries can't be empty.")
  (let ((cls (make-array n :initial-element '())))
    (let ((ee (copy-list entries)))
      (rplacd (last ee) ee) ;; ee is entries changed to a circular list
      (dotimes-f (i m)
        (dotimes-f (j n)
	  (push (pop ee) (svref cls j)))))
    (reset-markowitz
     (make-csparse :m m :n n
		   :cols (map 'vector
			   #'(lambda (col)
			       (input-sparse-v (nreverse col) make-sp))
			   cls)
		   :rlen (make-array m :initial-element -1)
		   :clen (make-array n :initial-element -1)))))

(defun make-zero-and-id (m n i0 j0 s &optional (make-sp #'make-sp-z))
  "Returns an m-by-n csparse with all 0's except that the square
block starting at i0,j0 and of side s has 1's on the diagonal.
make-sp should construct an appropriate sparse-elt from an index and
value.  make-sp defaults to the constructor over the ring of integers Z."
  (declare (type nnfixnum m n i0 j0 s))
  (let ((A (make-csparse-zero m n)))
    (with-csparse-slots (cols rlen clen) A
      (do ((k 0 (1+ k))
	   (i1 i0 (1+ i1))
	   (j1 j0 (1+ j1)))
	  ((>= k s) A)
	(declare (type nnfixnum k i1 j1))
	(push (funcall make-sp i1 1) (svref cols j1))
	(incf (svref rlen i1))
	(incf (svref clen j1))))))

(defun csparse-copy (A)
  "Returns a copy of the csparse A, sharing no structure with A itself."
  (with-csparse-slots (m n cols rlen clen) A
    (make-csparse :m m :n n
		  :cols (map 'vector #'copy-list cols)
		  :rlen (copy-seq rlen)
		  :clen (copy-seq clen))))

(defmethod m-num-cols ((A csparse))
  (with-csparse-slots (n) A
    n))

(defmethod m-num-rows ((A csparse))
  (with-csparse-slots (m) A
    m))

(defmethod mat ((A csparse))
  "Just returns A."
  A)

(defmethod print-object ((A csparse) stream)
  (with-csparse-slots (m n cols) A
    (if (or (= m 0) (= n 0) (> n 15) (> m 60))
        (format stream "[CSPARSE ~D by ~D]" m n)
      (let ((arr (make-array (list m n) :initial-element "0"))
            (widths (make-array n :initial-element 1)))
	(dotimes-f (j n)
	  (dolist (elt (svref cols j))
	    (let ((str (sp-print-value elt nil)))
	      (maxf (svref widths j) (length str))
	      (setf (aref arr (sp-i elt) j) str))))
        (dotimes-f (i m)
          (format stream "~&")
          (dotimes-f (j n)
            (format stream (format nil "~~~D<~~A~~>" (1+ (svref widths j)))
                    (aref arr i j))))))))

(defmethod print-entries ((A csparse) &optional (stream t))
  "Prints all the non-zero entries of the csparse A to the
stream in column-major order with syntax
m n
i j val
i j val..."
  (with-csparse-slots (m n cols) A
    (format stream "~&~D ~D" m n)
    (dotimes-f (j n)
      (dolist (ae (the sparse-v (svref cols j)))
	(format stream "~&~D ~D " (sp-i ae) j)
	(sp-print-value ae stream)))
    (format stream "~&")))

(defun update-census (A j census)
  "Updates A's rlen and clen after we've altered column j with one
of the sparse-v functions that returns a census."
  (with-csparse-slots (rlen clen) A
    (let ((sum 0))
      (declare (fixnum sum))
      (dolist (k census)
	(declare (fixnum k))
	(cond ((>= k 0)
	       (incf (svref rlen k))
	       (incf sum))
	      (t
	       (decf (svref rlen (the fixnum (- -1 k))))
	       (decf sum))))
      (incf (svref clen j) sum))))

(defun alter-col (A j1 fac j2)
  "In the csparse A, applies v-alter to the indicated columns.  Returns A.
Like v-alter, the code assumes we're in a domain, not simply a commutative
ring with identity."
  (with-csparse-slots (cols) A
    (multiple-value-bind (ans census) (v-alter (svref cols j1) fac (svref cols j2))
      (setf (svref cols j1) ans)
      (update-census A j1 census))
    A))

(defun alter-row (A i1 fac i2)
  "Like alter-col, but operates on the indicated rows."
  (if (sp-zerop fac)
      A
    (with-csparse-slots (n cols) A
      (dotimes-f (j n A)
        (multiple-value-bind (ans census) (v-alter-elt (svref cols j) i1 fac i2)
	  (setf (svref cols j) ans)
	  (update-census A j census))))))

(defun swap-cols (A j1 j2)
  "In the csparse A, interchanges the indicated columns.  Returns A."
  (with-csparse-slots (cols clen) A
    (psetf (svref cols j1) (svref cols j2)
           (svref cols j2) (svref cols j1))
    (psetf (svref clen j1) (svref clen j2)
	   (svref clen j2) (svref clen j1))
    A))

(defun swap-rows (A i1 i2)
  "In the csparse A, interchanges the indicated rows.  Returns A."
  (declare (type nnfixnum i1 i2))
  (if (= i1 i2)
      A
    (if (> i1 i2)
        (swap-rows A i2 i1)
      (with-csparse-slots (n cols rlen) A
        (dotimes-f (j n)
	  (v-swap-f (svref cols j) i1 i2))
	(psetf (svref rlen i1) (svref rlen i2)
	       (svref rlen i2) (svref rlen i1))
	A))))

(defun negate-col (A j)
  "In the csparse A, multiplies column j by -1.  Returns A."
  (with-csparse-slots (cols) A
    (v-negate-f (svref cols j))
    A))

(defun negate-row (A i)
  "In the csparse A, multiplies row i by -1.  Returns A."
  (with-csparse-slots (n cols) A
    (dotimes-f (j n A)
      (v-negate-elt-f (svref cols j) i))))

(defun sparsity (A &optional (corner 0))
  "Finds the ratio (number of non-zero entries)/(total number of
entries) in the southeast region [corner,m)-by-[corner,n) of the
csparse A of size m by n.  Returns it as a single-float between 0 and 1.
Columns with all 0's in the southeast region are not counted.  Requires
that the northeast region [0,corner)-by-[corner,n) have no non-zeroes."
  (declare (type nnfixnum corner))
  (with-csparse-slots (m n clen) A
    (assert (<= 0 corner m) ()
      "Corner ~D out of range [0,~D]." corner m)
    (let ((elt-ct 0)
	  (col-ct 0))
      (declare (integer elt-ct) (type nnfixnum col-ct))
      (do ((j corner (1+ j)))
	  ((>= j n))
	(declare (type nnfixnum j))
	(let ((cl (svref clen j)))
	  (declare (fixnum cl))
	  (when (> cl -1)
	    (incf elt-ct (the nnfixnum (1+ cl)))
	    (incf col-ct))))
      (let ((denom (* col-ct (- m corner))))
	(declare (integer denom))
	(if (zerop denom)
	    0.0f0
	  (coerce (/ elt-ct denom) 'single-float))))))

;; TO DO: add something to the sparse-elt contract so per-sparse-elt
;; is known directly.  The 16 is only accurate when a sparse-elt is a
;; cons, and then only in certain implementations.
(defun mem-count (A &optional (per-sparse-elt 16))
  "Returns the number of bytes consumed by the sparse-elts in the
csparse A, together with the conses forming the backbone of the
sparse-v's.  The optional argument should be the number of bytes
in one sparse-elt plus one cons for the backbone."
  (with-csparse-slots (clen) A
    (* per-sparse-elt
       (reduce #'+ clen
	       :initial-value (length clen))))) ;; to catch the -1's

(defmethod m-zerop ((A csparse))
  (with-csparse-slots (cols) A
    (every #'endp cols)))

(defmethod m-add ((a1 csparse) (a2 csparse))
  "Returns the matrix sum.  Doesn't alter a1 or a2."
  (with-csparse-slots ((m1 m) (n1 n) (cols1 cols)) a1
    (with-csparse-slots ((m2 m) (n2 n) (cols2 cols)) a2
      (assert (and (= m1 m2) (= n1 n2)) (a1 a2)
        "Dim mismatch: ~D by ~D versus ~D by ~D" m1 n1 m2 n2)
      (reset-markowitz
       (make-csparse :m m1 :n n1
		     :cols (map 'vector #'v-add-nondestr cols1 cols2)
		     :rlen (make-array m1 :initial-element -1)
		     :clen (make-array n1 :initial-element -1))))))

(defmethod m-subtract ((a1 csparse) (a2 csparse))
  "Returns the matrix difference.  Doesn't alter a1 or a2."
  (with-csparse-slots ((m1 m) (n1 n) (cols1 cols)) a1
    (with-csparse-slots ((m2 m) (n2 n) (cols2 cols)) a2
      (assert (and (= m1 m2) (= n1 n2)) (a1 a2)
        "Dim mismatch: ~D by ~D versus ~D by ~D" m1 n1 m2 n2)
      (reset-markowitz
       (make-csparse :m m1 :n n1
		     :cols (map 'vector #'v-subtract-nondestr cols1 cols2)
		     :rlen (make-array m1 :initial-element -1)
		     :clen (make-array n1 :initial-element -1))))))

(defmethod m-negate ((A csparse))
  "Returns the matrix negative.  Doesn't alter A."
  (with-csparse-slots (m n cols rlen clen) A
    (make-csparse :m m :n n
		  :cols (map 'vector #'v-negate-nondestr cols)
		  :rlen (copy-seq rlen)
		  :clen (copy-seq clen))))

(defun csparse-get (A i j)
  "Returns the sparse-elt giving the i,j-th entry of the csparse A,
or nil if the value is zero there."
  (with-csparse-slots (cols) A
    (v-get (svref cols j) i)))

(defun csparse-set (A i-and-val j)
  "Destructively alters the csparse A so the i,j-th elt has value v,
where i-and-val is a sparse-elt with index i and value v.  Returns
the altered A."
  (with-csparse-slots (cols) A
    (multiple-value-bind (ans census) (v-set (svref cols j) (sp-i i-and-val) i-and-val)
       (setf (svref cols j) ans)
       (update-census A j census))
    A))

(defmacro do-rows-csparse ((row-var A &optional end-form) &body body)
  "Executes its body for i = 0, 1, ..., with row-var bound to a
sparse-v holding the i-th row of the csparse A."
  (with-gensyms (popper m n i j cols)
    `(with-csparse-slots ((,m m) (,n n) (,cols cols)) ,A
       (let ((,popper (copy-seq ,cols)))
	 (declare (simple-vector ,popper))
         (dotimes-f (,i ,m ,end-form)
           (let ((,row-var '()))
             (declare (type sparse-v ,row-var))
             (do ((,j (1- ,n) (1- ,j)))
                 ((< ,j 0) ,@body)
	       (declare (fixnum ,j))
               (unless (endp (svref ,popper ,j))
                 (when (= ,i (sp-i (first (svref ,popper ,j))))
                   (push (copy-sp (pop (svref ,popper ,j)) ,j)
                         ,row-var))))))))))

(defmethod m-mult ((A csparse) (B csparse))
  "Returns the matrix product A * B of two csparses.  Doesn't alter A or B."
  (with-csparse-slots (m n) A
    (with-csparse-slots ((n0 m) (p n) (cols-b cols)) B
      (assert (= n n0) (A B)
        "Inner dimensions don't match: ~D by ~D vs ~D by ~D." m n n0 p)
      (let ((C (make-csparse-zero m p))
	    (i 0))
        (declare (type nnfixnum i))
	(with-csparse-slots (cols rlen clen) C
          (do-rows-csparse (row A)
	    (dotimes-f (j p)
	      (let ((prod (v-dot row (svref cols-b j))))
		(unless (or (null prod) (sp-zerop prod))
		  (push (copy-sp prod i) (svref cols j))
		  (incf (svref rlen i))
		  (incf (svref clen j)))))
	    (incf i))
	  (map-into cols #'nreverse cols))
	C))))

(defmethod m-product-zerop ((A csparse) (B csparse))
  "Whether the product A * B is zero.  Doesn't store the product."
  (with-csparse-slots (m n) A
    (with-csparse-slots ((n0 m) (p n) (cols-b cols)) B
      (assert (= n n0) (A B)
        "Inner dimensions don't match: ~D by ~D vs ~D by ~D." m n n0 p)
      (do-rows-csparse (row A t)
        (dotimes-f (j p)
	  (let ((prod (v-dot row (svref cols-b j))))
	    (unless (or (null prod) (sp-zerop prod))
	      (return-from m-product-zerop nil))))))))

(defmethod m-mult ((e perm2) (A csparse))
  "Destructively modifies A by swapping rows i1 and i2."
  (with-perm2-slots e
    (swap-rows A i1 i2)))

(defmethod m-mult ((A csparse) (e perm2))
  "Destructively modifies A by swapping columns i1 and i2."
  (with-perm2-slots e
    (swap-cols A i1 i2)))

(defmethod m-mult ((e perm) (A csparse))
  "Destructively modifies A by permuting its rows, yielding e*A."
  (with-csparse-slots (m n cols rlen) A
    (let ((m0 (length (the simple-vector (perm-arr e)))))
      (declare (type nnfixnum m0))
      (assert (= m0 m) (e A)
	"Dim mismatch: ~D-by-~D perm times ~D-by-~D csparse." m0 m0 m n))
    (dotimes-f (j n)
      (setf (svref cols j) (perm-times-sparse-v e (svref cols j))))
    (perm-times-vector e rlen)
    A))

(defmethod m-mult ((A csparse) (e perm))
  "Destructively modifies A by permuting its columns, yielding A*e."
  (with-csparse-slots (m n cols clen) A
    (let ((n0 (length (the simple-vector (perm-arr e)))))
      (declare (type nnfixnum n0))
      (assert (= n n0) (A e)
	"Dim mismatch: ~D-by-~D csparse times ~D-by-~D perm." m n n0 n0))
    (let ((e-tr (m-transpose e)))
      (declare (type perm e-tr))
      (perm-times-vector e-tr cols)
      (perm-times-vector e-tr clen)
      A)))

(defmethod m-mult ((e transv) (A csparse))
  "Destructively modifies A by adding v times row j to row i."
  (with-transv-slots e
    (with-transv-slot-i e
      (alter-row A i i-and-v j))))

(defmethod m-mult ((A csparse) (e transv))
  "Destructively modifies A by adding v times column i to column j."
  (with-transv-slots e
    (with-transv-slot-i e
      (alter-col A j i-and-v i))))

(defmethod m-id-p ((A csparse))
  (with-csparse-slots (m n cols clen) A
    (if (/= m n)
	nil
      (if (notevery #'(lambda (cl) (zerop (the fixnum cl))) clen)
	  nil
        (dotimes-f (j n t)
	  (let ((e (first (the sparse-v (svref cols j)))))
	    (unless (and (= j (sp-i e)) (sp-onep e))
	      (return nil))))))))

(defmethod m-transpose ((A csparse))
  "Returns the transpose of the csparse A.  Destroys A in the process."
  (with-csparse-slots (m n cols) A
    (let ((Atr (make-csparse-zero n m)))
      (do ((j (1- n) (1- j)))
          ((< j 0))
        (let ((colj (svref cols j)))
          (declare (type sparse-v colj))
          (setf (svref cols j) '())
          (till (endp colj)
            (let ((e (pop colj)))
              (csparse-set Atr (copy-sp e j) (sp-i e))))))
      (setf (csparse-rlen Atr) (copy-seq (csparse-clen A))
	    (csparse-clen Atr) (copy-seq (csparse-rlen A)))
      Atr)))

(defun csparse-concat-left-right (A B)
  "Returns a new csparse obtained by putting A and B side by side.
The number of rows is the maximum of the inputs' number of rows."
  (with-csparse-slots ((m1 m) (n1 n) (cols1 cols) (rlen1 rlen) (clen1 clen)) A
    (with-csparse-slots ((m2 m) (n2 n) (cols2 cols) (rlen2 rlen) (clen2 clen)) B
      (let ((m3 (max m1 m2))
	    (n3 (+ n1 n2)))
	(let ((c (make-csparse-zero m3 n3)))
	  (with-csparse-slots ((cols3 cols) (rlen3 rlen) (clen3 clen)) c
	    (dotimes-f (j n1)
	      (setf (svref cols3 j) (copy-list (svref cols1 j))
		    (svref clen3 j) (svref clen1 j)))
	    (do ((j 0 (1+ j))
		 (j2 n1 (1+ j2)))
		((= j n2))
	      (declare (type nnfixnum j j2))
	      (setf (svref cols3 j2) (copy-list (svref cols2 j))
		    (svref clen3 j2) (svref clen2 j)))
	    (dotimes-f (i m3)
	      (when (< i m1)
		(incf (svref rlen3 i)
		      (the nnfixnum (1+ (the fixnum (svref rlen1 i))))))
	      (when (< i m2)
		(incf (svref rlen3 i)
		      (the nnfixnum (1+ (the fixnum (svref rlen2 i))))))))
	  c)))))

(defmethod integrity-check ((A csparse) &key (message ""))
  "Checks the array bounds, the integrity of each column, and the
consistency of the Markowitz arrays."
  (with-csparse-slots (m n cols) A
    (assert (= n (length cols)) (A)
      "~An = ~D, length cols = ~D." message n (length cols))
    (map nil #'(lambda (col)
		 (integrity-check col :message message :m m))
	 cols))
  (test-markowitz A :message message))

(defun to-counter (A delta width height counter)
  "Helper method for csw-set-counter.  Overwrites counter to show A's
sparsity pattern.  counter is a one-dimensional array storing a
width-by-height rectangular array of numbers in column-major order.
We count the number of non-zeroes in each delta-by-delta submatrix of
A, and write the number into the corresponding entry of counter."
  (declare (type nnfixnum delta width height)
           (type (array (signed-byte 32) *) counter))
  (with-csparse-slots (n cols) A
    (fill counter 0)
    (do ((pj 0 (1+ pj))
	 (hpj 0 (+ hpj height)))
	((= pj width))
      (declare (type nnfixnum pj hpj))
      (do ((j (* pj delta) (1+ j))
           (j0 0 (1+ j0)))
          ((or (>= j n) (>= j0 delta)))
        (declare (type nnfixnum j j0))
        (dolist (ae (svref cols j))
	  (let ((k (+ (the nnfixnum (truncate (sp-i ae) delta)) hpj)))
	    (declare (type nnfixnum k))
	      (incf (aref counter k))))))))

;;; ------------------------------------------------------------

(defvar *verbose* nil
  "If true while reducing a csparse, print comments and timing data
to std output.  Default is nil.")

(defun time-stamp ()
  "Returns 03:05:17 to mean 17 seconds after 3:05 a.m."
  (multiple-value-bind (s m h) (get-decoded-time)
    (declare (type (integer 0 23) h) (type (integer 0 59) m s))
    (format nil "~2,'0D:~2,'0D:~2,'0D" h m s)))

;;; -------------------- Block Triangularization --------------------

(defvar *block-tri-rep-ct* 25
  "block-triangularize-3 will repeat its inner loop up to this many times
trying to shrink the current diagonal blocks.")

(defvar *suppress-permute-rows-onto-diag* nil
  "Bind to t during block-triangularization loops when you've already
called permute-rows-onto-diag once and know the number of diagonal
entries can't be improved.  Not to be changed by the user.")

(defun permute-rows-onto-diag (A)
  "Alters the csparse A by permuting rows so that there are
as many elements on the diagonal as possible.
Returns a perm P so that P * [resulting A] = [original A].
  The problem as stated only makes sense if m >= n.  For instance,
given the 1 by 2 matrix [0 1], the best solution is to pad with
zeros and get [0 0 / 0 1].  This code will give a warning, and
possibly crash later, if m < n.  (Within Sheafhom's own code,
permute-rows-onto-diag is only used when m >= n.)"
  (with-csparse-slots (m n cols) A
    (let ((P (make-id-perm m)))
      ;; Zeroth try.
      (when *suppress-permute-rows-onto-diag*
	(return-from permute-rows-onto-diag P))
      #|
      ;; First try: call out to Java's wandlmap.DigraphBipartite.match
      ;; Digraph vertices are [0,n) for col indices, [n,n+m) for rows.
      (block java-version
	(when (< m n)
	  (cerror "Keep going anyway."
		  "~&You've called permute-rows-onto-diag on a ~D by ~D matrix.~&This algorithm will likely crash unless m >= n.  Please consider~&taking the transpose of your matrix beforehand, re-transposing~&afterwards, and interpreting the P's as Q's." m n))
	(let ((f-to-java (format nil "dg~D.txt" (new-file-counter)))
	      (f-from-java (format nil "dg~D.txt" (new-file-counter))))
	  (with-open-file (si f-to-java :direction :output :if-exists :supersede)
	    (dotimes-f (j n)
	      (dolist (e (svref cols j))
		(let ((i (sp-i e)))
		  (declare (type nnfixnum i))
		  (format si "~D ~D ~D~&" j (+ i n) (if (= i j) 1 0))))))
	  (let ((cmd (format nil "java -Xmx400M -classpath \\wandl;\\linj_1.7 wandlmap.DigraphBipartite ~A,~A" f-to-java f-from-java))) ;; hard-coded for Mark's PC
	    (when *verbose*
	      (format t "~&Calling java's DigraphBipartite on ~D by ~D, ~A" m n (time-stamp)))
	    (excl:run-shell-command cmd :wait t :show-window :hide) ;; not ANSI CL
	    (delete-file f-to-java)
	    (unless (probe-file f-from-java)
	      (return-from java-version)) ;; goto Duff, Erisman and Reed version
	    (when *verbose*
	      (format t "~&Exiting java ~A" (time-stamp))))
	  (let ((match (make-array n :initial-element -1))) ;; j -> i
	    (block read-f-from-java
	      (with-open-file (so f-from-java)
		(loop
		  (let ((j (read so nil)))
		    (if (null j)
			(return-from read-f-from-java)
		      (progn
			(assert (and (<= 0 j) (< j n)) ()
			  "j = ~D in ~A out of range." j f-from-java)
			(assert (= (svref match j) -1) ()
			  "j = ~D occurs twice in ~A." j f-from-java)
			(let ((i (- (read so t) n)))
			  (assert (and (<= 0 i) (< i m)) ()
			    "i = ~D in ~A out of range." i f-from-java)
			  (setf (svref match j) i))))))))
	    (delete-file f-from-java)
	    (let ((j 0))
	      (declare (type nnfixnum j))
	      (till (>= j n)
		(let ((i (svref match j)))
		  (declare (fixnum i))
		  (cond ((or (= i -1) (= j i))
			 (incf j))
			(t
			 (swap-rows A i j)
			 (perm-swap-cols P i j)
			 ;; Where i is in the image, reset the image to j.
			 (setf (svref match j) j)
			 ;; If j is in the image, reset the image to i.
			 (dotimes-f (j0 n) ;; speed up?
			   (unless (= j0 j)
			     (when (= (svref match j0) j)
			       (setf (svref match j0) i)
			       (return))))
			 (setq j 0)))))) ;; speed up?
	    (when *verbose*
	      (format t "~&Put ~D out of ~D onto diagonal ~A" (count-on-diagonal A) (min m n) (time-stamp)))
	      (return-from permute-rows-onto-diag P))))
	      |#
      ;; Second try: Duff, Erisman and Reid, _Direct Methods for Sparse
      ;; Matrices_, 6.3.  The implementation is slow because it doesn't
      ;; use the tricks that sections 6.3 and 6.5 advise.
      (when (< m n)
	(cerror "Keep going anyway."
		"~&You've called permute-rows-onto-diag on a ~D by ~D matrix.~&This algorithm works better when m >= n.  Please consider~&taking the transpose of your matrix beforehand, re-transposing~&afterwards, and interpreting the P's as Q's." m n))
      (let ((dim (min m n))
	    (k -1)
	    (k-stack '())
	    (col-stack '()))
	(declare (type nnfixnum dim) (fixnum k) (list k-stack col-stack))
	(loop
	  (if (endp k-stack)
	      (let ((k1 (1+ k)))
		(declare (type nnfixnum k1))
		(if (>= k1 dim)
		    (return P) ;; the one and only exit
		  (setq k k1
			k-stack (list k1)
			col-stack (list (svref cols k1)))))
	    (macrolet ((head-col () `(the sparse-v (first col-stack))))
	      (let ((cheap (head-col)))
		(declare (type sparse-v cheap))
		(till (or (endp cheap) (>= (sp-i (first cheap)) k))
		  (pop cheap))
		(cond (cheap
		       (setf (head-col) cheap)
		       (setq P
			 (permute-rows-onto-diag-aux
			  A k P k-stack col-stack))
		       (setq k-stack '() col-stack '()))
		      ((endp (head-col))
		       (pop k-stack)
		       (pop col-stack)
		       (when col-stack
			 (pop (head-col))))
		      (t
		       (let ((r (sp-i (first (head-col)))))
			 (declare (type nnfixnum r))
			 (cond ((>= r n)
				(setf (head-col) '()))
			       ((member r k-stack :test #'=)
				(pop (head-col)))
			       (t
				(push r k-stack)
				(push (svref cols r) col-stack))))))))))))))

(defun permute-rows-onto-diag-aux (A k P k-stack col-stack)
  "Helper for permute-rows-onto-diag.  Does the actual job of
permuting A's rows.  Returns the perm P with the new permutations
factored in."
  (declare (type csparse A) (type nnfixnum k) (type perm P)
	   (list k-stack col-stack))
  ;;; From here to +++ is for testing only.
  (assert (= (length k-stack) (length col-stack)) ()
      "Unequal stack lengths...~&k-stack = ~A~&col-stack cars = ~A"
      k-stack (mapcar #'first col-stack))
  (let ((k-test (butlast k-stack 1))
	(c-test (mapcar #'(lambda (v) (sp-i (first v)))
			(rest col-stack))))
    (assert (equal k-test c-test) ()
      "~&I don't understand the stacks...~&k-stack = ~A~&col-stack cars = ~A"
      k-stack (mapcar #'first col-stack)))
  ;; +++
  (let* ((last-r (sp-i (first (first col-stack))))
	 (abcd (list last-r)))
    (declare (type nnfixnum last-r))
    (dolist (c (butlast k-stack 1))
      (push c abcd))
    (till (or (endp abcd) (endp (rest abcd)))
      (let ((i1 (first abcd))
	    (i2 (second abcd)))
	(declare (type nnfixnum i1 i2))
	(unless (= i1 i2)
	  (swap-rows A i1 i2)
	  (perm-swap-cols P i1 i2))
	(pop abcd)))
    (unless (= k last-r)
      (swap-rows A k last-r)
      (perm-swap-cols P k last-r))
    P))

(defun count-on-diagonal (A)
  "Returns the number of i such that the csparse A has a non-zero
entry in the (i,i) position."
  (with-csparse-slots (m n cols) A
    (let ((dim (min m n))
	  (ans 0))
      (declare (type nnfixnum dim ans))
      (dotimes-f (i dim ans)
	(when (v-get (svref cols i) i)
	  (incf ans))))))

;;; A csparse is a directed graph--more precisely, implements the
;;; strongly-conn functions--in the following way.  We restrict to the
;;; upper/left square of size dim := (min m n).  The graph has 0, 1,
;;; ..., dim-1 as the vertices, and conses (j . i) as the edges when
;;; column j has an entry in row i with i < dim.

(defmethod strongly-conn-vertices ((A csparse))
  "A set whose iterator returns 0, 1, ..., dim-1 in order.
Here dim = (min m n), where A is m-by-n."
  (iota (strongly-conn-num-vertices A)))

(defmethod strongly-conn-num-vertices ((A csparse))
  "Returns (min m n), where A is m-by-n."
  (with-csparse-slots (m n) A
    (min m n)))

;;; To do(?): implement with lazy sets, not hash-sets.
(defmethod strongly-conn-edges-from ((A csparse) j)
  (declare (type nnfixnum j))
  (with-csparse-slots (cols) A
    (let ((dim (strongly-conn-num-vertices A))
	  (col (svref cols j))
	  (h (make-hash-table :test #'equalp)))
      (declare (type nnfixnum dim) (type sparse-v col))
      (dolist (e col)
	(let ((i (sp-i e)))
	  (declare (type nnfixnum i))
	  (if (>= i dim)
	      (return)
	    (unless (= j i)
	      (put-with-equalp-key (cons j i) h)))))
      (make-hash-set h))))

(defmethod strongly-conn-ending-vertex ((A csparse) e)
  (cdr (the cons e)))

;;; TO DO: optional keywords :use-p, :use-q, with default t, to
;;; suppress saving P and Q if they're unwanted.
(defun block-triangularize (A)
  "Alters the csparse A by permuting rows and columns to bring it to
block upper-triangular form.  Uses the strongly-conn functions, whose
implementations are taken from Even's book [q.v.], though the ideas
come from Duff, Erisman and Reid, _Direct Methods for Sparse Matrices_,
ch. 6.
  Calls permute-rows-onto-diagonal beforehand to try to put
entries onto the diagonal.  If the diagonal is full of entries, the
block triangularization is the best possible.
  The function only considers the dim-by-dim square block,
where dim = (min m n) for an m-by-n matrix.  When m < n, see
block-triangularize-2, which gets the right-hand columns into the
act.  When m > n, the result will not really be upper-triangular in
general in the range of rows m <= i < n.
  Returns three values: the list of sizes of the blocks, and two perm
objects P, Q so that P * [resulting A] * Q = [original A]."
  (with-csparse-slots (m n cols) A
    (let ((scc-list '())
	  (rp-P (make-id-perm m))
	  (rp-Q-tr (make-id-perm n))
	  (dim (min m n)))
      (declare (list scc-list) (type perm rp-P rp-Q-tr) (type nnfixnum dim))
      (when (> dim 0)
	(if (>= m n)
	    (setq rp-P (permute-rows-onto-diag A))
	  (let ((tr (m-transpose A))) ;; m < n
	    (setq rp-Q-tr (permute-rows-onto-diag tr))
	    (let ((y (m-transpose tr)))
	      (map-into cols #'identity (csparse-cols y))
	      (reset-markowitz A))))
	(setq scc-list (strongly-conn-scc A))
	(let ((flat-scc-list '()))
	  (dolist (scc scc-list) ;; CLISP choked on (apply #'append scc-list)
	    (dolist (k scc)
	      (push k flat-scc-list)))
	  (do ((i1-list (nreverse flat-scc-list) (rest i1-list))
	       (i0 0 (1+ i0)))
	      ((endp i1-list)
	       (assert (= i0 dim) () "i1-list wrong length."))
	    (declare (list i1-list) (type nnfixnum i0))
	    (let ((i1 (first i1-list)))
	      (declare (type nnfixnum i1))
	      (unless (= i0 i1)
		(swap-rows A i0 i1)
		(swap-cols A i0 i1)
		(setq i1-list (nsubst i1 i0 i1-list)) ;; speed up
		;; Also (nsubst i0 i1 ...), but that's moot.
		(perm-swap-cols rp-P i0 i1)
		(perm-swap-cols rp-Q-tr i0 i1))))
	  (when (<= m n) ;; test clause
	    (do ((tail (mapcar #'length scc-list) (rest tail))
		 (left 0))
		((endp tail))
	      (let ((right (+ left (first tail))))
		;; The test: for left <= j < right, i's must be < right.
		(do ((j left (1+ j)))
		    ((>= j right))
		  (when (svref cols j)
		    (assert (< (sp-i (first (last (svref cols j)))) right) ()
		      "Not triangular in the [~D, ~D) diagonal square."
		      left right)))
		(setq left right))))))
      (values (mapcar #'length scc-list) rp-P (m-transpose rp-Q-tr)))))

(defun block-triangularize-2 (A &optional (paint-hook nil))
  "Calls (block-triangularize A) one or more times.  If m >= n, calls
it only once.  If m < n, tries repeatedly to improve the result by
swapping columns from the [m,n) range into the [0,m) range.  Returns
the same three values as block-triangularize, except that we omit
the Q's (the third value Q is always nil)."
  ;; Remembering the Q's wouldn't be hard.
  (let ((sz-l-latest '())
	(sz-l-short '())
	(sz-l-count 1)
	p-accum)
    (declare (list sz-l-latest sz-l-short) (type nnfixnum sz-l-count))
    (labels ((update-latest-sorted ()
	       (let ((ans (sort (copy-list (remove 1 sz-l-latest)) #'<)))
		 (if (equal sz-l-short ans)
		     (incf sz-l-count)
		   (setq sz-l-short ans sz-l-count 1))
		 (when paint-hook
		   (funcall paint-hook)))))
      (multiple-value-bind (sz-l P Q) (block-triangularize A) ;; first time
	(declare (list sz-l) (type perm P) (ignore Q))
	(setq sz-l-latest sz-l p-accum P))
      (update-latest-sorted)
      (when *verbose*
	(format t "~&Block-triangularize-2 initial size list [no 1's, sorted] ~A~&  ~S" (time-stamp) sz-l-short))
      (with-csparse-slots (m n cols) A
	(when (< m n)
	  (let ((*suppress-permute-rows-onto-diag* t) ;; after first time
		(has-jj nil)
		(ks-in-j (make-hash-table))
		(js-last-i -1)
		(improved t))
	    (declare (fixnum js-last-i))
	    (labels ((cache-j-data (j)
		       (declare (type nnfixnum j))
		       (setq has-jj nil)
		       (clrhash ks-in-j)
		       (setq js-last-i -1)
		       (do ((tail (svref cols j) (rest tail)))
			   ((endp tail))
			 (let ((i (sp-i (first tail))))
			   (declare (type nnfixnum i))
			   (if (= i j)
			       (setq has-jj t)
			     (when (> i j)
			       (puthash i t ks-in-j)))
			   (when (endp (rest tail))
			     (setq js-last-i i))))))
	      (loop while (and improved (< sz-l-count 25)) do
		    (when *verbose*
		      (format t "~&Starting block-triangularize-2 double loop ~A" (time-stamp)))
		    (setq improved nil)
		    (dotimes-f (j m)
		      (cache-j-data j)
		      (do ((k (1+ j) (1+ k)))
			  ((>= k n))
			;; j < k because otherwise a swap might make col j
			;; stick out below the diagonal block j used to be
			;; in.  Another possibility: only take k to the
			;; right of j's block.
			(declare (type nnfixnum k))
			(let ((has-kj (has-key k ks-in-j))
			      (has-jk nil)
			      (has-kk nil)
			      (ks-last-i -1))
			  (declare (fixnum ks-last-i))
			  (do ((tail (svref cols k) (rest tail)))
			      ((endp tail))
			    (let ((i (sp-i (first tail))))
			      (declare (type nnfixnum i))
			      (if (= i j)
				  (setq has-jk t)
				(when (= i k)
				  (setq has-kk t)))
			      (when (endp (rest tail))
				(setq ks-last-i i))))
			  (when (< ks-last-i js-last-i)
			    (unless (and has-jj (not has-jk))
			      (unless (and has-kk (not has-kj))
				(swap-cols A j k)
				(cache-j-data j)
				(setq improved t)))))))
		    (when improved
		      (multiple-value-bind (sz-l P Q) (block-triangularize A)
			(declare (list sz-l) (type perm P) (ignore Q))
			(setq sz-l-latest sz-l)
			(m-mult p-accum P))
		      (update-latest-sorted)
		      (when *verbose*
			(if (= sz-l-count 1)
			    (format t "~&Size list [no 1's, sorted] ~A~&  ~S" (time-stamp) sz-l-short)
			  (format t "~&Size list repeated ~D times ~A" sz-l-count (time-stamp)))))))))))
    (values sz-l-latest p-accum nil)))

(defun block-triangularize-3 (A &optional (paint-hook nil))
  "Calls (block-triangularize A) one or more times.  If m >= n, calls
it only once.  If m < n, tries repeatedly to improve the result by
swapping columns from the [m,n) range into the [0,m) range.  Returns
the same three values as block-triangularize, except that we omit
the Q's (the third value Q is always nil)."
  ;; Remembering the Q's wouldn't be hard.
  (let ((sz-l-latest '())
	(sz-l-short '())
	(sz-l-count 1)
	p-accum)
    (declare (list sz-l-latest sz-l-short) (type nnfixnum sz-l-count))
    (labels ((update-latest-sorted ()
	       (let ((ans (sort (copy-list (remove 1 sz-l-latest)) #'<)))
		 (if (equal sz-l-short ans)
		     (incf sz-l-count)
		   (setq sz-l-short ans sz-l-count 1))
		 (when paint-hook
		   (funcall paint-hook)))))
      (multiple-value-bind (sz-l P Q) (block-triangularize A) ;; first time
	(declare (list sz-l) (type perm P) (ignore Q))
	(setq sz-l-latest sz-l p-accum P))
      (update-latest-sorted)
      (when *verbose*
	(format t "~&Block-triangularize-3 initial size list [no 1's, sorted] ~A~&  ~S" (time-stamp) sz-l-short))
      (with-csparse-slots (m n cols) A
	(when (< m n)
	  (let ((*suppress-permute-rows-onto-diag* t) ;; after first time
		(last-i-arr (make-array n))
		(has-jj nil)
		(ks-in-j (make-hash-table))
		(improved t))
	    (declare (simple-vector last-i-arr))
	    (macrolet ((last-i (l)
			 `(the fixnum (svref last-i-arr ,l))))
	      (labels ((cache-last-i-data ()
			 (dotimes-f (j n)
			   (setf (last-i j)
			     (aif (svref cols j)
				  (sp-i (first (last it)))
			       -1))))
		       (cache-j-data (j)
			 (declare (type nnfixnum j))
			 (setq has-jj nil)
			 (clrhash ks-in-j)
			 (do ((tail (svref cols j) (rest tail)))
			     ((endp tail))
			   (let ((i (sp-i (first tail))))
			     (declare (type nnfixnum i))
			     (when (>= i j)
			       (if (= i j)
				   (setq has-jj t)
				 (puthash i t ks-in-j)))))))
		(cache-last-i-data)
		(loop while (and improved (< sz-l-count *block-tri-rep-ct*)) do
		      (when *verbose*
			(format t "~&Starting block-triangularize-3 double loop ~A" (time-stamp)))
		      (setq improved nil)
		      (do ((j 0 (1+ j))
			   (jb 0) ;; j in current diagonal block
			   (sz-l-tail sz-l-latest))
			  ((= j m))
			(declare (type nnfixnum j jb))
			(cache-j-data j)
			(when (= jb (first sz-l-tail))
			  (pop sz-l-tail)
			  (setq jb 0))
			(do ((k (+ j (- (first sz-l-tail) jb)) (1+ k)))
			    ((>= k n))
			  (declare (type nnfixnum k))
			  ;; We tried caching the values
			  ;; min{(last-i k0) for k0 >= k}
			  ;; and quitting the k loop as soon as this
			  ;; min was >= (last-i j).  The goal was to
			  ;; speed up the code, but in fact it made it
			  ;; slightly slower.
			  (when (< (last-i k) (last-i j))
			    (let ((has-jk nil)
				  (has-kk nil)
				  (k-geq-m (>= k m)))
			      (do ((tail (svref cols k) (rest tail)))
				  ((endp tail))
				(let ((i (sp-i (first tail))))
				  (declare (type nnfixnum i))
				  (if (= i j)
				      (setq has-jk t)
				    (if (and k-geq-m (> i j))
					(return)
				      (when (>= i k)
					(when (= i k)
					  (setq has-kk t))
					(return))))))
			      (unless (and has-jj (not has-jk))
				(unless (and has-kk (not (has-key k ks-in-j)))
				  (swap-cols A j k)
				  (psetf (last-i j) (last-i k)
					 (last-i k) (last-i j))
				  (cache-j-data j)
				  (setq improved t)))))))
		      (when improved
			(multiple-value-bind (sz-l P Q) (block-triangularize A)
			  (declare (list sz-l) (type perm P) (ignore Q))
			  (setq sz-l-latest sz-l)
			  (m-mult p-accum P))
			(update-latest-sorted)
			(cache-last-i-data)
			(when *verbose*
			  (if (= sz-l-count 1)
			      (format t "~&Size list [no 1's, sorted] ~A~&  ~S" (time-stamp) sz-l-short)
			    (format t "~&Size list repeated ~D times ~A" sz-l-count (time-stamp))))))))))))
    (values sz-l-latest p-accum nil)))

#|
(defun block-triangularize-4-test (A &optional (depth '()))
  "Find a maximal row-column matching with non-zero entries, using the
java version of permute-rows-onto-diag.  Imagine permuting the matched
rows and columns to the upper-right [northeast] corner with the
matched non-zeroes on the diagonal.  Then the southwest corner is
empty, and we can recursively try the same approach on the nw and se
regions.  This function creates the regions recursively and prints out
the details in a tree format.  If the test shows there is a large tree
where both the nw and se branches are non-empty, then A is a good
candidate for block triangularization.  [Unfortunately, experiments
show the matrices from eqco4N.lisp almost always have empty se
blocks.]"
  (with-csparse-slots (m n cols) A
    (let ((f-to-java (format nil "dg~D.txt" (new-file-counter)))
	  (f-from-java (format nil "dg~D.txt" (new-file-counter)))
	  (eff-i-set (make-hash-table :size m))
	  (eff-j-count 0))
      (when (m-zerop A)
	(format t "~&~S empty" depth)
	(return-from block-triangularize-4-test))
      (with-open-file (si f-to-java :direction :output :if-exists :supersede)
	(dotimes-f (j n)
	  (when (svref cols j)
	    (dolist (e (svref cols j))
	      (let ((i (sp-i e)))
		(format si "~D ~D ~D~&" j (+ i n) (if (= i j) 1 0))
		(setf (gethash i eff-i-set) t)))
	    (incf eff-j-count))))
      (let ((cmd (format nil "java -Xmx400M -classpath \\wandl;\\linj_1.7 wandlmap.DigraphBipartite ~A,~A" f-to-java f-from-java))) ;; hard-coded for Mark's PC
	(excl:run-shell-command cmd :wait t :show-window :hide) ;; not ANSI CL
	(assert (probe-file f-from-java))
	(delete-file f-to-java))
      (let ((match-j-set (make-hash-table :size n))
	    (match-i-set (make-hash-table :size (hash-table-count eff-i-set))))
	(block read-f-from-java ;; find a match j -> i
	  (with-open-file (so f-from-java)
	    (loop
	      (let ((j (read so nil)))
		(if (null j)
		    (return-from read-f-from-java)
		  (progn
		    (assert (and (<= 0 j) (< j n)) ()
		      "j = ~D in ~A out of range." j f-from-java)
		    (let ((i (- (read so t) n)))
		      (assert (and (<= 0 i) (< i m)) ()
			"i = ~D in ~A out of range." i f-from-java)
		      (setf (gethash j match-j-set) t)
		      (setf (gethash i match-i-set) t))))))))
	(delete-file f-from-java)
	(format t "~&~S, eff ~D by ~D, matched ~D" depth (hash-table-count eff-i-set) eff-j-count (hash-table-count match-j-set))
	(let ((A-nw (csparse-copy A))
	      (A-se A)) ;; an alias
	  (with-csparse-slots ((cols-nw cols)) A-nw
	    ;; Delete all matched columns, and assert that all that
	    ;; remains lies in the matched rows.
	    (dotimes-f (j n)
	      (if (has-key j match-j-set)
		  (setf (svref cols-nw j) '())
		(dolist (e (svref cols-nw j))
		  (assert (has-key (sp-i e) match-i-set)))))
	    (reset-markowitz A-nw))
	  (with-csparse-slots ((cols-se cols)) A-se
	    ;; Delete all matched rows, and assert that all that
	    ;; remains lies in the matched columns.
	    (dotimes-f (j n)
	      (setf (svref cols-se j)
		(remove-if #'(lambda (e) (has-key (sp-i e) match-i-set))
			   (svref cols-se j)))
	      (when (svref cols-se j)
		(assert (has-key j match-j-set))))
	    (reset-markowitz A-se))
	  ;; Recurse.
	  (block-triangularize-4-test A-nw (cons :nw depth))
	  (block-triangularize-4-test A-se (cons :se depth)))))))
|#

;;; A second idea (7/25/2007)...  Let C be a constant a lot larger
;;; than m + n.  In permute-rows-onto-diag, change the max capacity of
;;; a j->i edge to be C - (#(col j) + #(row i) - 1).  Initial flow is
;;; either = max capacity or 0, the way it is now.  Change the max
;;; capacity of each ss->v and v->tt edge to C.  Then, we hope, the
;;; max flow will still determine a matching: check that every
;;; j-vertex has non-zero flow on exactly one edge leaving j, that
;;; this flow is of max capacity, and conversely at every i.  If it is
;;; a matching, it will tend to be a matching with low overall
;;; Markowitz count.

;;; ----- Main methods for matrix reduction (Smith normal form) -----

(defvar *show-stats* nil
  "If true while reducing a csparse, pop up graphs of the changing
sparsity and number of elementary matrices.  Default is nil.")
(defvar *show-csw* nil
  "If true while reducing a csparse, show the sparsity pattern in real
time.  Note: this will slow down the computation significantly.
Default is nil.")

(defvar *allow-markowitz* t
  "If true (the default), use the pure Markowitz pivoting algorithm.
Whether it's true or false, (pivot-method ...) gives a text description
of the algorithm(s) in use.")

(defvar *allow-block-tri* nil
  "If true, put a csparse into block upper-triangular form as part of the
reduction process.  The default is nil.")

(defvar *allow-lll* nil
  "If true, permit Lenstra-Lenstra-Lovasz while reducing a csparse.
Requires D = Z.  Default is nil.")
(defvar *lll-width* 200
  "Use Lenstra-Lenstra-Lovasz on strips of columns up to this wide.")
(defvar *lll-threshold* 0.1
  "Permit Lenstra-Lenstra-Lovasz when sparsity > this number.")
(defvar *lll-next-try* 50
  "After one run of Lenstra-Lenstra-Lovasz, don't do another until the
active region has moved over this many columns.")

(defvar *allow-minor-trick* nil
  "If true, allow the minor trick.  Default is nil.  Temp files
minorNN.txt, where NN is an integer, will be written to the current
working directory.") ;; write more
(defvar *minor-trick-threshold* 0.1
  "Permit the minor trick when sparsity > this number.")
(defvar *minor-trick-col-func*
    #'(lambda (m0) (floor 30000000 m0))
  ;; 40M entries * 16 bytes/entry [see comment on mem-count's optional
  ;; argument] = 640Mbytes.  The example quoted at
  ;; *resize-areas-threshold* had not crashed at 670Mbytes when a lot
  ;; of resize-areas calls were happening and no P's were stored in
  ;; RAM.  ...3 Jan 2007: no, it did crash at 40M entries in
  ;; disk-hnf-base step, so go to 30M.
  "A function of one variable, the number of rows m0.  Returns
a number n0 of columns.  This applies when we're reducing a large
m-by-n csparse.  We're saying that by the time the number of
rows in the active region has decreased from m to m0, we figure
we can still reduce an m0-by-n0 csparse, even if it's close to
100% dense.")
;;; TO DO: hit-with-minor trick uses sp-v.  As of this writing
;;; (11/22/2007), that's a macro defined in the sparse-elt-p*.lisp
;;; files, but not over Z.  Yet we don't get errors when compiling
;;; over Z.  Figure out why.

(defvar *allow-wiedemann-winnow* nil)
(defvar *wiedemann-winnow-threshold* 0.20)

(defvar *inside-field-p* nil
  "Whether we're a csparse reduction algorithm and the underlying
domain D is a field.  Set by the system; not to be changed by the
user.")

(defvar *inside-f_p-p* nil
  "If we're a csparse reduction algorithm and the underlying domain D is
the field F_p of prime order, this variable will be p; otherwise it
will be nil.  Set by the system; not to be changed by the user.")

(defvar *allow-disk-hnf* nil
  "If true, permit disk-based Hermite normal form while reducing a csparse.
Default is nil.  Temp files hnfNN.txt, where NN is an integer, will be
written to and deleted from the current working directory.")
(defvar *disk-hnf-threshold* 0.0
  "Start disk-based Hermite normal form when sparsity > this number.")
(defvar *disk-hnf-width*
    #'(lambda (m0)
	(funcall *minor-trick-col-func* m0))
; 	(declare (type nnfixnum m0))
; 	(if *inside-f_p-p*
;  	    (floor 25000000 ;; max # 32-bit words for one dense-matrix-mod-p
;  		   (max m0 1))
; 	  1000))
  "Disk-based Hermite normal form divides the matrix into strips
this wide, then recombines them with a sort.  m0 is the effective
number of rows, e.g., m - corner within jac.  If the strip is
going to be stored in a dense matrix, make sure the total number
of entries is less than array-total-size-limit.")
(defvar *disk-hnf-batch-size* nil
  "Disk-based Hermite normal form adds this many columns at a time.
When nil [the default], uses the value of (disk-hnf-width m0).")
(defvar *disk-hnf-sort-width* 1000
  "disk-hnf-sort sorts this many columns at a time in RAM.")

(defvar *allow-modular-hnf* nil) ;; doc pending
(defvar *modular-hnf-threshold*
    #'(lambda (m n corner sparsity)
	(declare (ignore m n corner))
	(>= sparsity 0.5))) ;; doc pending

(defun rev-lists (filename-in filename-out)
  "Converts a text file with contents (a b c)(d e f g)(h i)(j k l)
to a text file with contents (j k l)(h i)(d e f g)(a b c), while
holding at most one list at a time in RAM.  More precisely, identifies
intervals of text with balanced parentheses, and writes the intervals
in reverse order.  For instance, (a b) dog (c d) would
become (c d) god (a b)."
  (with-open-file (s-in filename-in :element-type '(unsigned-byte 8))
    (let ((n (file-length s-in)))
      (assert n () "Couldn't find the length of ~A." filename-in)
      (with-open-file (s-out filename-out
		       :direction :output
		       :element-type '(unsigned-byte 8)
		       :if-exists :supersede)
	(let ((junk-byte (char-int #\?)))
	  (dotimes (i n)
	    (write-byte junk-byte s-out)))
	(let ((buf (make-array 30
			       :element-type '(unsigned-byte 8)
			       :adjustable t
			       :fill-pointer 0))
	      (left-paren (char-int #\())
	      (right-paren (char-int #\)))
	      (paren-count 0)
	      (i 0))
	  (till (= i n)
	    (let ((c (read-byte s-in)))
	      (vector-push-extend c buf)
	      (incf i)
	      (if (= c left-paren)
		  (incf paren-count)
		(when (= c right-paren)
		  (decf paren-count)
		  (assert (>= paren-count 0) ()
		    "Too many right parentheses at position ~D." (1- i))))
	      (when (zerop paren-count)
		(let ((moved (file-position s-out (- n i))))
		  (assert moved () "Couldn't move ~A to position ~D."
			  filename-out (- n i))
		  (write-sequence buf s-out)
		  (setf (fill-pointer buf) 0)))))
	  (assert (zerop paren-count) ()
	    "Too few left parentheses at the end."))))))

(defvar *file-counter* 0
  "For the private use of new-file-counter.")

(defun new-file-counter ()
  (prog1 *file-counter* (incf *file-counter*)))

(defmacro do-snf-stem ((list-slot list-direction file-stem var A &optional (result nil)) &body body)
  (with-gensyms (pq fc lyst stream item)
    `(with-slots ((,pq p-q-to-file) (,fc file-counter) (,lyst ,list-slot)) ,A
       (if ,pq
	   (block file-version
	     (with-open-file (,stream
			      (format nil "~A~D.txt" ,file-stem ,fc)
			      :direction :input)
	       (loop
		 (let ((,item (read ,stream nil)))
		   (if (null ,item)
		       (return-from file-version ,result)
		     (let ((,var (ecase (first ,item)
				   (:P (make-perm2 (second ,item) (third ,item)))
				   (:PN (make-perm (second ,item)))
				   (:T (make-transv (second ,item) (third ,item))))))
		       ,@body))))))
	 (dolist (,var (,list-direction ,lyst) ,result)
	   ,@body)))))

(defmacro do-snf-p ((var A &optional (result nil)) &body body)
  `(do-snf-stem (p-list identity "snfp" ,var ,A ,result) ,@body))

(defmacro do-snf-p-rev ((var A &optional (result nil)) &body body)
  `(do-snf-stem (p-list reverse "snfb" ,var ,A ,result) ,@body))

(defmacro do-snf-q ((var A &optional (result nil)) &body body)
  `(do-snf-stem (q-list identity "snfq" ,var ,A ,result) ,@body))

(defmacro do-snf-q-rev ((var A &optional (result nil)) &body body)
  `(do-snf-stem (q-list reverse "snfh" ,var ,A ,result) ,@body))

(defclass snf ()
  ((mat :type (or csparse null) :reader mat :initarg :mat
	:documentation
	"Holds the csparse whose snf this is.  Or holds nil
if the snf was computed destructively.  The function 'mat'
applied to an snf returns this value.")
   (d :type csparse :initarg :d)
   (use-p :initarg :use-p)
   (use-q :initarg :use-q)
   (p-q-to-file :initarg :p-q-to-file)
   (file-counter :initarg :file-counter)
   (p-list :type list :initform '())
   (q-list :type list :initform '()))
  (:documentation
   "Holds the Smith normal form of a csparse.  Documented at make-snf."))

(defun snf-diagonal-p (A)
  "Whether the csparse A has the form of the 'd' documented in make-snf."
  (with-csparse-slots (m n cols) A
    (let ((first-zero n))
      (declare (type nnfixnum first-zero))
      ;; Is it diagonal up to the first zero?
      (do ((j 0 (1+ j)))
	  ((or (= j m) (>= j first-zero)))
	(declare (type nnfixnum j))
	(if (endp (svref cols j))
	    (setq first-zero j)
	  (unless (and (endp (rest (svref cols j)))
		       (= j (sp-i (first (svref cols j)))))
	    (return-from snf-diagonal-p nil))))
      ;; Is it all zero after the first zero?
      (do ((j (1+ first-zero) (1+ j)))
	  ((>= j n))
	(declare (type nnfixnum j))
	(unless (endp (svref cols j))
	  (return-from snf-diagonal-p nil)))
      ;; Does the non-zero part satisfy d0 | d1 | d2 | ...?
      (do ((j 0 (1+ j))
	   (k 1 (1+ k)))
	  ((>= k first-zero) t)
	(unless (sp-divides (first (svref cols j)) (first (svref cols k)))
	  (return-from snf-diagonal-p nil))))))

(defun minor-trick-stem (file-counter)
  (format nil "minor~D" file-counter))

(defgeneric rank (A)
  (:documentation
   "The rank of A over the field of fractions of D.  If D = Z, this is
the rank over Q.  If D is a field, it is the rank in the usual sense--the
dimension of the image.  It is the number of non-zero elementary divisors
in the snf.  Note: (rank A) = (num-units A) + (length (torsion A))."))

(defmethod rank ((A snf))
  (with-csparse-slots (n cols) (slot-value A 'd)
    (aif (position-if #'endp cols) it n)))

(defgeneric num-units (A)
  (:documentation
   "The number of units among the elementary divisors of A.  See 'rank'."))

(defmethod num-units ((A snf))
  (with-csparse-slots (n cols) (slot-value A 'd)
    (aif (position-if #'(lambda (col)
			  (declare (type sparse-v col))
			  (or (endp col) (not (sp-unitp (first col)))))
		      cols)
	 it
      n)))

(defgeneric torsion (A)
  (:documentation
   "A list of sparse-elts whose values are the non-units among the
non-zero elementary divisors of a.  Each value divides the one to
its right.  The indices are nu, nu+1, ..., for nu = (num-units A).
See 'rank'."))

(defmethod torsion ((A snf))
  (let ((ans '()))
    (declare (list ans))
    (with-csparse-slots (n cols) (slot-value A 'd)
      (dotimes-f (j n)
	(let ((col (svref cols j)))
	  (declare (type sparse-v col))
	  (if (endp col)
            (return)
	    (unless (sp-unitp (first col))
	      (push (first col) ans)))))
      (nreverse ans))))

(defun m-image-contained-in-image (A B)
  "Whether the image of the csparse A is contained in the image of
the snf B."
  (declare (type csparse A) (type snf B))
  (let ((C (csparse-copy A)))
    (declare (type csparse C))
    (with-slots (d use-p) B
      (declare (type csparse d))
      (assert use-p ()
	"The second argument was computed without remembering the~&changes of coords on the target side.")
      (do-snf-p (p B)
	(m-mult (m-inverse p) C))
      ;; Now C should have arbitrary entries in rows where d has a
      ;; unit, entries divisible by the torsion in rows where d has
      ;; torsion, and 0 in rows where d has 0.
      (let ((nu (num-units B))
	    (r (rank B)))
	(declare (fixnum nu r))
	(with-csparse-slots (n cols) C
	  (dotimes-f (j n t)
	    (dolist (e (svref cols j))
	      (let ((i (sp-i e)))
		(declare (type nnfixnum i))
		(when (or (>= i r)
			  (and (>= i nu)
			       (not (sp-divides (csparse-get d i i) e))))
		  (return-from m-image-contained-in-image nil))))))))))

(defmethod m-ker ((A snf) &optional (make-sp #'make-sp-z))
  "See the documentation on defgeneric m-ker.  make-sp defaults to the
constructor over the ring of integers Z."
  (assert (slot-value A 'use-q) ()
    "Can't take ker of an snf where the q's aren't stored.")
  (with-csparse-slots (n) (slot-value A 'd)
    (let ((r (rank A)))
      (declare (type nnfixnum r))
      (let ((mm (make-zero-and-id (- n r) n 0 r (- n r) make-sp)))
        (declare (type csparse mm))
        (do-snf-q (q A)
          (m-mult mm (m-inverse-transpose q)))
	(m-transpose mm)))))

(defmethod m-ker-retraction ((A snf) &optional (make-sp #'make-sp-z))
  "Returns a csparse that's a retraction for (ker A).  That is, the
retraction has linearly independent rows, and the product
 (ker-retraction A) * (ker A) is the identity.  [The product the other
way around need not be the identity.]  make-sp should construct an
appropriate sparse-elt from an index and value.  make-sp defaults to
the constructor over the ring of integers Z."
  (assert (slot-value A 'use-q) ()
    "Can't take ker-retraction of an snf where the q's aren't stored.")
  (with-csparse-slots (n) (slot-value A 'd)
    (let ((r (rank A)))
      (declare (type nnfixnum r))
      (let ((mm (make-zero-and-id (- n r) n 0 r (- n r) make-sp)))
        (declare (type csparse mm))
        (do-snf-q (q A mm)
          (m-mult mm q))))))

(defmethod m-coker-section ((A snf) &optional (make-sp #'make-sp-z))
  "Provisional version that works over the field of fractions of D,
ignoring torsion.  make-sp should construct an
appropriate sparse-elt from an index and value.  make-sp defaults to
the constructor over the ring of integers Z."
  (assert (slot-value A 'use-p) ()
    "Can't take coker-section of an snf where the p's aren't stored.")
  (with-csparse-slots (m) (slot-value A 'd)
    (let ((r (rank A)))
      (declare (type nnfixnum r))
      (let ((mm (make-zero-and-id (- m r) m 0 r (- m r) make-sp)))
	(declare (type csparse mm))
	(do-snf-p-rev (p A (m-transpose mm))
	  (m-mult mm (m-transpose p)))))))

(defmethod m-coker ((A snf) &optional (make-sp #'make-sp-z))
  "Provisional version that works over the field of fractions of D,
ignoring torsion.  make-sp should construct an
appropriate sparse-elt from an index and value.  make-sp defaults to
the constructor over the ring of integers Z."
  (assert (slot-value A 'use-p) ()
    "Can't take coker of an snf where the p's aren't stored.")
  (with-csparse-slots (m) (slot-value A 'd)
    (let ((r (rank A)))
      (declare (type nnfixnum r))
      (let ((mm (make-zero-and-id (- m r) m 0 r (- m r) make-sp)))
	(declare (type csparse mm))
	(do-snf-p-rev (p A mm)
	  (m-mult mm (m-inverse p)))))))

;;; One can also define m-image, m-image-retraction, m-coimage,
;;; m-coimage-section, and the canonical map from the image to the
;;; coimage.

(defmethod m-num-cols ((A snf))
  (m-num-cols (the csparse (slot-value A 'd))))

(defmethod m-num-rows ((A snf))
  (m-num-rows (the csparse (slot-value A 'd))))

(defmethod m-zerop ((A snf))
  (m-zerop (the csparse (slot-value A 'd))))

(defmethod print-object ((A snf) stream)
  (with-csparse-slots (m n cols) (slot-value A 'd)
    (let ((u (num-units A)))
      (declare (type nnfixnum u))
      (format stream "~&[SNF ~D by ~D, [~R unit~:P]" m n u)
      (do ((j u (1+ j)))
	  ((or (= j n) (endp (the sparse-v (svref cols j)))))
	(format stream " ")
	(sp-print-value (first (the sparse-v (svref cols j))) stream))
      (format stream "]"))))

(defmethod integrity-check ((A snf) &key (message "") (orig (mat A)))
  "The optional key :orig should give a copy of the original csparse.
It can be omitted if the snf was built non-destructively."
  (with-slots (d use-p use-q) A
    (declare (type csparse d))
    (integrity-check d :message message)
    (with-csparse-slots (m n) d
      (do-snf-p (elem A)
	(integrity-check elem :message message :n m))
      (do-snf-q (elem A)
	(integrity-check elem :message message :n n)))
    (when (and orig use-p use-q)
      (let ((b (csparse-copy d)))
	(do-snf-p-rev (elem A)
	  (m-mult elem b))
	(do-snf-q (elem A)
	  (m-mult b elem))
	(assert (equalp b orig) (A)
	  "~AIntegrity error in snf.~&ORIGINAL~&~A~&RESULT~&~A"
	  message orig b)))))

;;; ----------------------------------------

(defun pivot (d corner use-q last-lll)
  "Finds the next pivot for jac to use.  The algorithm is affected
by several of the global variables.  Returns three values,
i j pivot-as-sparse-elt, or 0 0 nil."
  (declare (type csparse d) (type nnfixnum corner) (fixnum last-lll))
  (if *allow-markowitz*
      (pivot-markowitz d corner)
    (if *inside-field-p*
	(pivot-light-low d corner)
      (progn
	(unless use-q
	  (if (< last-lll 0)
	      (sort-by-tmarkowitz d corner)
	    (with-csparse-slots (cols) d
				(sort-by-norm-sq cols corner))))
	(with-csparse-slots (cols) d
			    (pivot-greedy cols corner))))))

(defun pivot-method ()
  "Returns a string describing the algorithm[s] 'pivot') will use."
  (let ((args '()))
    (if *allow-markowitz*
	(push "Pure Markowitz." args)
      (if *inside-field-p* ;; next two out of date?  check.
	  (push "Light low column, then greedy." args)
	(push "Sort to lower right, then greedy." args)))
    (if *allow-block-tri*
	(push "Block-tri." args)
      (push "No block-tri." args))
    (when *allow-lll*
      (push (format nil "LLL at sparsity > ~5,3F" *lll-threshold*) args))
    (when *allow-minor-trick*
      (push (format nil "Minor trick at sparsity ~5,3F" *minor-trick-threshold*) args))
    (when *allow-wiedemann-winnow*
      (push (format nil "Wiedemann-winnow at sparsity ~5,3F" *wiedemann-winnow-threshold*) args))
    (when *allow-disk-hnf*
      (push (format nil "Disk HNF at sparsity > ~5,3F" *disk-hnf-threshold*) args))
    (when (and *allow-modular-hnf* (not *inside-field-p*))
      (push (format nil "Modular HNF.") args))
    (unless (or *allow-lll* *allow-minor-trick* *allow-wiedemann-winnow* *allow-disk-hnf* (and *allow-modular-hnf* (not *inside-field-p*)))
      (push "No LLL, minor trick, Wiedemann winnow, disk HNF or modular HNF." args))
    (format nil "~{~A  ~}" (nreverse args))))

(defun pivot-light-low (A corner)
  "Find the lightest columns in the range j >= corner, and among the
them find the one whose starting i is greatest.  Return that sparse-elt,
without regard to the Euclidean norm of its value."
  (with-csparse-slots (n cols clen) A
    (let ((best-i 0)
	  (best-j 0)
	  (best-elt nil)
	  (best-clen nil))
      (declare (type nnfixnum best-i best-j))
      (do ((j corner (1+ j)))
	  ((>= j n) (values best-i best-j best-elt))
	(let ((col (svref cols j))
	      (cl (svref clen j)))
	  (declare (type sparse-v col) (fixnum cl))
	  (when col
	    (when (or (null best-clen) (< cl (the fixnum best-clen)))
	      (setq best-clen (svref clen j))
	      (let* ((e (first col))
		     (i (sp-i e)))
		(declare (type nnfixnum i))
		(when (or (null best-elt) (> i best-i))
		  (setq best-i i best-j j best-elt e))))))))))

(defun sort-by-tmarkowitz (A corner)
  "Sort the columns of the csparse A, in the range j >= corner, by the
number of non-zero entries.  Break ties by putting to the left the
column whose first index is bigger.  The result looks like several
triangular strips, hence the t in tmarkowitz."
  (declare (type nnfixnum corner))
  (with-csparse-slots (n cols clen) A
    (let ((arr (make-array (- n corner))))
      (do ((j corner (1+ j))
	   (j0 0 (1+ j0)))
	  ((>= j n))
	(declare (type nnfixnum j j0))
	(setf (aref arr j0) (cons (svref clen j) (svref cols j))))
      (sortf arr #'(lambda (l1 l2)
		     (declare (list l1 l2))
		     (let ((clen1 (first l1))
			   (clen2 (first l2)))
		       (declare (fixnum clen1 clen2))
		       (if (< clen1 clen2)
			   t
			 (if (> clen1 clen2)
			     nil
			   (if (= clen1 -1)
			       nil
			     (> (sp-i (first (rest l1)))
				(sp-i (first (rest l2))))))))))
      (do ((j corner (1+ j))
	   (j0 0 (1+ j0)))
	  ((>= j n))
	(declare (type nnfixnum j j0))
	(let ((aa (svref arr j0)))
	  (setf (svref clen j) (first aa)
		(svref cols j) (rest aa))))
      (fill arr '()) ;; gc-help
      (setq arr nil)))) ;; gc-help

(defun high-rank-light-front-minor (A corner)
  "Grabs the leftmost strictly lower-triangular block of the
csparse A in the range corner <= j < n, using a greedy algorithm, and
sorts so as to put this block at the front in columns corner,
corner+1, ....  Returns the altered A."
  (declare (type nnfixnum corner))
  (with-csparse-slots (m n cols) A
    (let ((dim (min m n)))
      (declare (type nnfixnum dim))
      (sort-by-tmarkowitz A corner)
      (labels ((hrl-aux (j0)
		 (declare (type nnfixnum j0))
		 (if (>= j0 dim)
		     (when *verbose*
		       (format t "~&high-rank-light-front-minor: done because ~D >= min(m,n)" j0))
		   (let ((top-i-to-j (make-hash-table :size (min m (- n j0))))
			 (j-max -1))
		     (declare (fixnum j-max))
		     (do ((j j0 (1+ j)))
			 ((= j n))
		       (declare (type nnfixnum j))
		       (let ((v (svref cols j)))
			 (declare (type sparse-v v))
			 (when v
			   (let ((i (sp-i (first v))))
			     (declare (type nnfixnum i))
			     (unless (has-key i top-i-to-j)
			       (puthash i j top-i-to-j)
			       (setq j-max j))))))
		     (let ((j-ct (hash-table-count top-i-to-j)))
		       (declare (type nnfixnum j-ct))
		       (if (< j-ct 2)
			   (when *verbose*
			     (format t "~&high-rank-light-front-minor: done because top is flat"))
			 (let ((j1 (+ j0 j-ct))
			       (j2 (1+ j-max))
			       (j-cols '()))
			   (declare (type nnfixnum j1 j2) (list j-cols))
			   (maphash #'(lambda (i j)
					(declare (ignore i))
					(push (svref cols j) j-cols)
					(setf (svref cols j) '()))
				    top-i-to-j)
			   (let ((subarr (subseq cols j0 j2)))
			     (declare (simple-vector subarr))
			     (setq subarr
			       (stable-sort subarr
					    #'(lambda (v1 v2)
						"Nils left, all else right."
						(declare (type sparse-v v1 v2))
						(and (endp v1)
						     (not (endp v2))))))
			     (do ((j j0 (1+ j)))
				 ((endp j-cols)
				  (assert (= j j1) () "Count wrong: [j0, j1)."))
			       (declare (type nnfixnum j))
			       (setf (svref cols j) (pop j-cols)))
			     (let ((j j0))
			       (declare (type nnfixnum j))
			       (map nil #'(lambda (subv)
					    (declare (type sparse-v subv))
					    (if (< j j1)
						(assert (endp subv) () "Nonnil?")
					      (setf (svref cols j) subv))
					    (incf j))
				    subarr)
			       (assert (= j j2) () "Count wrong: [j1, j2).")))
			   (when *verbose*
			     (format t "~&high-rank-light-front-minor: full-rank strip [~D, ~D)." j0 j1))
			   (hrl-aux j1))))))))
	(hrl-aux corner))
      (reset-markowitz A))))

;;; ------------------------------ Disk HNF ------------------------------

(defun new-disk-hnf-filename ()
  (format nil "hnf~D.txt" (new-file-counter)))

(defun disk-hnf-width (m0)
  "When you cut a matrix in half, and the left half has only one
column, disk-hnf-last1-to-2 can produce an infinite loop.  Hence
this function returns the max of *disk-hnf-width* and 4."
  (max (funcall *disk-hnf-width* m0) 4))

(defmacro do-sparse-v-stream ((v in-stream) &body body)
  (with-gensyms (s)
    `(let ((,s ,in-stream))
       (do ((,v (read ,s nil '()) (read ,s nil '())))
	   ((endp ,v))
	 (declare (type sparse-v ,v))
	 ,@body))))

(defvar *do-sparse-v-list-stream-limit* 1000000
  "do-sparse-v-list-stream will buffer its input in RAM until about
this number of sparse-elt's has been read.")

(defmacro do-sparse-v-list-stream ((vv in-stream) &body body)
  "in-stream is an input stream that will produce zero or more
non-null sparse-v's.  The macro runs the body with the symbol vv bound
to successive sublists of the sparse-v's.  For instance, vv might be
bound to the first 1000 sparse-v's, then to the next 1000, then to
the next 997, etc.  We use buffering in RAM: see
*do-sparse-v-list-stream-limit*."
  (with-gensyms (s elt-ct eof v1)
    `(let ((,s ,in-stream))
       (loop
	 (let ((,vv '())
	       (,elt-ct 0)
	       ,eof)
	   (declare (list ,vv) (type nnfixnum ,elt-ct))
	   (do ((,v1 (read ,s nil '()) (read ,s nil '())))
	       (nil)
	     (declare (type sparse-v ,v1))
	     (when ,v1
	       (push ,v1 ,vv)
	       (incf ,elt-ct (length ,v1)))
	     (setq ,eof (null ,v1))
	     (when (or ,eof (>= ,elt-ct *do-sparse-v-list-stream-limit*))
	       (return)))
	   (setq ,vv (nreverse ,vv))
	   ,@body
	   (setq ,vv '()) ;; gc-help
	   (when ,eof
	     (return))))))) ;; done

(defun hit-with-disk-hnf (A &key (i0 0) (start 0) (end nil))
  "Removes all columns j in [start,end) from the csparse A, runs
hnf-lower-tri or a dense algorithm on these columns a certain number
at a time until the whole thing is in Hermite normal form, and puts
the result back into A.  The i-th row of A must be zero for all
0 <= i < i0.  Returns the altered A.  Defaults: i0 0, start 0,
end n.
  Notation throughout disk-hnf: dhc... has the form hnf[integer].txt
and is the name of a file containing zero or more sparse-v's sorted
by disk-hnf-compare.  The empty sparse-v may not appear, and indeed
we use () as a signal for end-of-file.  The number of sparse-v's
must be a fixnum.  The overall goal is to put dhc files into
lower-triangular Hermite normal form.  The indices at the heads of
the columns may not be strictly increasing, though because of
disk-hnf-compare they will at least be increasing."
  (let ((dhc (new-disk-hnf-filename)) ;; see "...recursive-step" for doc
	(nc 0) ;; actual Number of non-zero Columns
	(do-it-yourself-p nil)
	(offset 0)
	(ring-name nil))
    (declare (type nnfixnum nc offset))
    #|
    (format t "~&It's time to write a large matrix to disk and column-reduce~&it from there.  Enter 1 to reduce it with your own~&program.  Enter another value to have Sheafhom reduce~&it with the disk-hnf routines.~&? ")
    (when (equal (read) 1)
      (setq do-it-yourself-p t
	    offset i0))
	    |#
    (with-csparse-slots (m n cols) A
      (unless end
	(setq end n))
      (assert (<= 0 start end n) ()
	"Out of range: need 0 <= start=~D <= end=~D <= n=~D" start end n)
      (let ((arr (make-array (- end start) :fill-pointer 0)))
	(do ((j start (1+ j)))
	    ((>= j end))
	  (declare (type nnfixnum j))
	  (when (svref cols j)
	    (vector-push (svref cols j) arr)
	    (when do-it-yourself-p
	      (unless ring-name
		(setf ring-name (sp-ring-name (first (svref cols j))))))
	    (setf (svref cols j) '())
	    (incf nc)))
	(sortf arr (if do-it-yourself-p
		       (complement #'disk-hnf-compare)
		     #'disk-hnf-compare))
	(with-open-file (so dhc :direction :output :if-exists :supersede)
	  (map nil #'(lambda (v)
		       (format-flat so "~S"
				    (if do-it-yourself-p
					(mapcar #'(lambda (elt) (from-x-to-cons (copy-sp elt (- (sp-i elt) offset)))) v)
				      v)))
	       arr))
	(fill arr '()) ;; gc-help
	(setq arr nil)) ;; gc-help
      (if do-it-yourself-p
	  (progn
	    (break "The matrix has been written to disk as ~A~&It has ~D rows; all row indices have ~D subtracted off.~&The entries are in ~A.~&Please store the reduced matrix under the same filename,~&then continue from this break." dhc (- m i0) i0 ring-name)
	    ;; Wait for the user to reduce it....
	    (format t "Enter 1 to skip reading the result back in.  If you skip~&it, you will have to edit the snf*.txt files by~&hand before doing anything with them.  Enter another~&value to read the result back in.~&? ")
	    (unless (equal (read) 1)
	      (with-open-file (si dhc)
		(do ((v (read si nil) (read si nil))
		     (j start (1+ j)))
		    ((null v)
		     (when *verbose*
		       (format t "~&Read ~D columns back in." (- j start))))
		  (declare (type nnfixnum j))
		  (assert (< j end) () "Reading in more than we wrote out.")
		  (setf (svref cols j)
		    (mapcar #'(lambda (elt) (copy-sp (from-cons-to-x elt) (+ (sp-i (from-cons-to-x elt)) offset))) v))))))
	(progn
	  (when *verbose*
	    (format t "~&    Starting hit-with-disk-hnf"))
	  (multiple-value-bind (il ir new-nc) (disk-hnf-recursive-step dhc i0 m nc)
	    (declare (ignore il ir) (type nnfixnum new-nc))
	    (with-open-file (si dhc)
	      (do ((v (read si nil) (read si nil))
		   (j start (1+ j)))
		  ((null v)
		   (assert (= j (+ start new-nc)) ()
		     "new-nc = ~D is inaccurate." new-nc))
		(declare (type nnfixnum j))
		(assert (< j end) () "Reading in more than we wrote out.")
		(setf (svref cols j) v))))))
      (do ((j start (1+ j)) ;; 'do' clause for testing only
	   (k (1+ start) (1+ k)))
	  ((>= k end))
	(declare (type nnfixnum j k))
	(if (svref cols j)
	    (assert (or (endp (svref cols k))
			(< (sp-i (first (svref cols j)))
			   (sp-i (first (svref cols k))))) ()
	      "Result not strictly lower-tri at cols ~D, ~D." j k)
	  (assert (endp (svref cols k)) ()
	    "Result has col ~D null and col ~D non-null." j k))))
    (unless do-it-yourself-p
      (delete-file dhc))
    (reset-markowitz A)))

(defun disk-hnf-recursive-step (dhc i0 m nc &optional (depth '()))
  "Input: name of a dhc file, and the number nc of sparse-v's in that
file.  Each sparse-v has indices i only in the range i0 <= i < m.
The file is overwritten with the lower-tri HNF.
  If we're in the left branch of the right branch of the right branch,
depth is (:l :r :r).  The symbol :r1 refers to disk-hnf-last1-to-2.
  Returns three values, the i's of the first and last sparse-v's and
the final number of sparse-v's.  Returns -1 -1 0 for a zero matrix.
  See hit-with-disk-hnf for documentation on 'dhc'."
  (declare (type nnfixnum nc))
  (if (<= nc (disk-hnf-width (- m i0)))
      ;;(if *inside-f_p-p*
      ;;(disk-hnf-f_p-base-step dhc i0 m nc depth)
      (disk-hnf-base-step dhc i0 m nc depth)
    ;;)
    (let ((dhc1 (new-disk-hnf-filename))
	  (dhc2 (new-disk-hnf-filename)))
      (let* ((nc1 (floor nc 2))
	     (nc2 (- nc nc1)))
	(declare (type nnfixnum nc1 nc2))
	(when *verbose*
	  (format t "~&    Recursive step, depth ~A, ~D cols ~A~&" depth nc (time-stamp)))
	(with-open-file (si dhc)
	  (let ((j 0)) ;; To do: these copies don't need to use read.
	    (with-open-file (so1 dhc1 :direction :output :if-exists :supersede)
	      (till (= j nc1)
		(format-flat so1 "~S" (read si t))
		(incf j)))
	    (with-open-file (so2 dhc2 :direction :output :if-exists :supersede)
	      (till (= j nc)
		(format-flat so2 "~S" (read si t))
		(incf j))))
	  (assert (null (read si nil)) () "dhc had over nc = ~D entries." nc))
	(multiple-value-bind (i2l i2r new-nc2)
	    (disk-hnf-recursive-step dhc2 i0 m nc2 (cons :r depth))
	  (setq nc2 new-nc2)
	  (let ((i1l -1) (i1r -1))
	    (setq nc1 (disk-hnf-clean dhc1 dhc2)) ;; beforehand
	    (loop
	      (multiple-value-bind (i1la i1ra temp-nc1)
		  (disk-hnf-recursive-step dhc1 i0 m nc1 (cons :l depth))
		(declare (ignore temp-nc1))
		(multiple-value-bind (new-nc1 clean-made-a-change)
		    (disk-hnf-clean dhc1 dhc2)
		  (setq nc1 new-nc1)
		  (unless clean-made-a-change
		    (setq i1l i1la i1r i1ra)
		    (return)))))
	    (cond ((< i1l 0)
		   (rename-file dhc2 dhc)
		   (delete-file dhc1)
		   (values i2l i2r nc2))
		  ((< i2l 0)
		   (rename-file dhc1 dhc)
		   (delete-file dhc2)
		   (values i1l i1r nc1))
		  ((> i2l i1r) ;; done
		   (let ((final-nc (disk-hnf-merge dhc1 dhc2 dhc)))
		     (assert (= (+ nc1 nc2) final-nc) ()
		       "Num cols messed up at end: ~D + ~D /= ~D."
		       nc1 nc2 final-nc)
		     (delete-file dhc1)
		     (delete-file dhc2)
		     (values i1l i2r final-nc)))
		  ((< i2l i1r)
		   (let ((new-nc (disk-hnf-merge dhc1 dhc2 dhc)))
		     (delete-file dhc1)
		     (delete-file dhc2)
		     (disk-hnf-recursive-step dhc (min i1l i2l) m new-nc depth)))
		  (t ;; (= i2l i1r)
		   (disk-hnf-last1-to-2 dhc1 dhc2)
		   (multiple-value-bind (new-i2l new-i2r new-nc2)
		       (disk-hnf-recursive-step dhc2 i1r m (1+ nc2) (cons :r1 depth))
		     (setq nc2 new-nc2)
		     (cond ((> nc1 1) ;; dhc1 non-empty
			    (disk-hnf-clean dhc1 dhc2 nil)
			    (let ((new-nc ;; next merge is really a concat
				   (disk-hnf-merge dhc1 dhc2 dhc)))
			      (assert (= (+ (1- nc1) nc2) new-nc) ()
				"Num cols messed up: ~D + ~D /= ~D."
				(1- nc1) nc2 new-nc)
			      (delete-file dhc1)
			      (delete-file dhc2)
			      (values i1l new-i2r new-nc)))
			   (t
			    (rename-file dhc2 dhc)
			    (delete-file dhc1)
			    (values new-i2l new-i2r nc2))))))))))))

(defun disk-hnf-merge (dhc1 dhc2 dhc)
  "dhc1 and dhc2 are dhc files.  We write the sparse-v's from both files to
dhc, merging them with disk-hnf-compare so the result is an dhc file.
Returns the number of sparse-v in dhc.
   See hit-with-disk-hnf for documentation on 'dhc'."
  (when *verbose*
    (format t "~&    Merging ~A~&" (time-stamp)))
  (with-open-file (so dhc :direction :output :if-exists :supersede)
    (macrolet ((w (v si)
		 `(progn
		    (format-flat so "~S" ,v)
		    (setq ,v (read ,si nil)))))
      (with-open-file (si1 dhc1)
	(with-open-file (si2 dhc2)
	  (let ((v1 (read si1 nil))
		(v2 (read si2 nil))
		(ct 0))
	    (till (and (null v1) (null v2))
	      (if (disk-hnf-compare v1 v2)
		  (w v1 si1)
		(w v2 si2))
	      (incf ct))
	    ct))))))

(defun disk-hnf-last1-to-2 (lt1 lt2)
  "lt1 and lt2 are dhc files that are strictly lower-triangular.
The last sparse-v of lt1 and the first sparse-v of lt2 must
have the same leading index i.
We remove the last sparse-v from lt1 and
put it into lt2, getting the two vectors sorted.  In the end,
lt1 is strictly lower-triangular and has one fewer element,
while lt2 is a dhc file, has one more element, and is
strictly lower-triangular if you don't count its first column.
   See hit-with-disk-hnf for documentation on 'dhc'."
  (let ((v-buffer '()))
    (let ((lt1-out (new-disk-hnf-filename)))
      (with-open-file (si1 lt1)
	(with-open-file (so1 lt1-out :direction :output :if-exists :supersede)
	  ;; To do: these copies don't need to use read.
	  (do-sparse-v-stream (v si1)
	    (when v-buffer
	      (format-flat so1 "~S" v-buffer))
	    (setq v-buffer v))))
      (rename-file lt1-out lt1))
    (let ((dhc2-out (new-disk-hnf-filename)))
      (with-open-file (so2 dhc2-out :direction :output :if-exists :supersede)
	(with-open-file (si2 lt2)
	  ;; To do: most of these copies don't need to use read.
	  (let ((v-buf2 (read si2 nil)))
	    ;; v-buf2 is nil iff lt2 had size 0
	    (when (and v-buf2 (disk-hnf-compare v-buf2 v-buffer))
	      (psetq v-buffer v-buf2
		     v-buf2 v-buffer))
	    (format-flat so2 "~S" v-buffer)
	    (when v-buf2
	      (format-flat so2 "~S" v-buf2)
	      (do-sparse-v-stream (v si2)
		(format-flat so2 "~S" v))))))
      (rename-file dhc2-out lt2))))

(defun disk-hnf-sort (f nc &optional (depth '()))
  "f is the name of a file of non-zero sparse-v's.  nc is the number
of sparse-v's.  We sort the sparse-v's by disk-hnf-compare and
overwrite the file with the result."
  (declare (type nnfixnum nc))
  (if (<= nc *disk-hnf-sort-width*)
      (let ((arr (make-array nc :fill-pointer 0)))
	(when *verbose*
	  (format t "~&        Sorting base step, depth ~A, ~D cols ~A" depth nc (time-stamp)))
	(with-open-file (si f)
	  (do-sparse-v-stream (v si)
	    (vector-push v arr)))
	(sortf arr #'disk-hnf-compare)
	(with-open-file (so f :direction :output :if-exists :supersede)
	  (map nil #'(lambda (v) (format-flat so "~S" v)) arr))
	(fill arr '()) ;; gc-help
	(setq arr nil)) ;; gc-help
    (let ((f1 (new-disk-hnf-filename))
	  (f2 (new-disk-hnf-filename)))
      (let* ((nc1 (floor nc 2))
	     (nc2 (- nc nc1)))
	(declare (type nnfixnum nc1 nc2))
	(when *verbose*
	  (format t "~&        Sorting, depth ~A, ~D cols ~A" depth nc (time-stamp)))
	(with-open-file (si f)
	  (let ((j 0))
	    (with-open-file (so1 f1 :direction :output :if-exists :supersede)
	      (till (= j nc1)
		(format-flat so1 "~S" (read si t))
		(incf j)))
	    (with-open-file (so2 f2 :direction :output :if-exists :supersede)
	      (till (= j nc)
		(format-flat so2 "~S" (read si t))
		(incf j))))
	  (assert (null (read si nil)) () "dhc had over nc = ~D entries." nc))
	(disk-hnf-sort f1 nc1)
	(disk-hnf-sort f2 nc2)
	(disk-hnf-merge f1 f2 f)
	(delete-file f1)
	(delete-file f2)))))

(defun disk-hnf-base-step (dhc i0 m nc depth)
  "dhc is a dhc file.  nc is the number of sparse-v's in that file.
The file is overwritten with the lower-tri HNF.
  Returns three values, the i's of the first and last sparse-v's and
the final number of sparse-v's.  Returns -1 -1 0 for a zero matrix.
   See hit-with-disk-hnf for documentation on 'dhc'."
  (when *verbose*
    (format t "~&    Base step, depth ~A, ~D cols ~A~&" depth nc (time-stamp)))
  (let ((v-in-hnf '())
	(batch-size (or *disk-hnf-batch-size* (disk-hnf-width (- m i0))))
	(si-at-eof nil))
    (declare (list v-in-hnf))
    (with-open-file (si dhc)
      (till si-at-eof
	(let ((v-read '()))
	  (declare (list v-read))
	  (do ((i 0 (1+ i)))
	      ((or si-at-eof (>= i batch-size)))
	    (declare (type nnfixnum i))
	    (let ((v (read si nil)))
	      (cond ((null v)
		     (setq si-at-eof t))
		    (t
		     (push v v-read)
		     (decf nc)))))
	  (unless (endp v-read)
	    (when (and *verbose* (or (> batch-size 1) (zerop (mod nc 100))))
	      (format t "~&    Starting hnf-lower-tri on ~D cols with ~D to go ~A~&" (+ (length v-in-hnf) (length v-read)) nc (time-stamp)))
	    (setq v-in-hnf
	      (hnf-lower-tri
	       (merge 'list v-in-hnf (nreverse v-read)
		      #'disk-hnf-compare)))))))
    (with-open-file (so dhc :direction :output :if-exists :supersede)
      (map nil #'(lambda (v) (format-flat so "~S" v)) v-in-hnf))
    (if (endp v-in-hnf)
	(values -1 -1 0)
      (multiple-value-prog1
	  (values (sp-i (first (first v-in-hnf)))
		  (sp-i (first (first (last v-in-hnf))))
		  (length v-in-hnf))
	(setq v-in-hnf nil))))) ;; gc-help

(defun disk-hnf-f_p-base-step (dhc i0 m nc depth)
  "Same contract as disk-hnf-base-step, but the underlying integral
domain D must be the field F_p of prime order and p must be the value
of *inside-f_p-p*."
  (assert (<= i0 m) () "Need i0 <= m.")
  (when *verbose*
    (format t "~&    Base step, depth ~A, ~D cols ~A~&" depth nc (time-stamp)))
  (let ((sample-elt nil))
    ;; Quick first pass to get a sample-elt.
    (with-open-file (si dhc)
      (do-sparse-v-stream (v si)
	(setq sample-elt (first v))
	(return)))
    (if (not sample-elt)
	(values -1 -1 0)
      (let* ((m0 (- m i0))
	     ;; aa is transposed because row-reduce-mod-p uses rows.
	     (aa (make-dense-matrix-mod-p-zero nc m0 *inside-f_p-p*))
	     (a (mat aa)))
	(declare (type nnfixnum m0) (type dense-matrix-mod-p aa) (vector a))
	(with-open-file (si dhc)
	  (let ((j 0))
	    (declare (type nnfixnum j))
	    (do-sparse-v-stream (v si)
	      (assert (<= i0 (sp-i (first v))) () "i0 is wrong.")
	      (dolist (e v)
		(setf (aref a (+ (* m0 j) (- (sp-i e) i0)))
		  (sp-integer-lift e)))
	      (incf j))
	    (assert (= j nc) () "Initial column count off.")))
	(let ((pivots (row-reduce-mod-p aa))
	      last-piv
	      (new-nc 0))
	  (declare (list pivots) (type nnfixnum new-nc))
	  (do ((l pivots (rest l)))
	      ((endp l))
	    (declare (list l))
	    (incf new-nc)
	    (unless (rest l)
	      (setq last-piv (first l))))
	  (with-open-file (so dhc :direction :output :if-exists :supersede)
	    (do ((i 0 (1+ i))
		 (new-nc-2 0))
		((= i nc)
		 (assert (= new-nc new-nc-2) ()
		   "Length of pivots /= number of non-zero rows."))
	      (declare (type nnfixnum i new-nc-2))
	      (let ((v '()))
		(declare (type sparse-v v))
		(do ((j (1- m0) (1- j)))
		    ((< j 0))
		  (declare (type fixnum j))
		  (let ((e (aref a (+ (* m0 i) j))))
		    (declare (integer e))
		    (unless (zerop e)
		      (push (sp-embed-z sample-elt e (+ i0 j)) v))))
		(when v
		  (format-flat so "~S" v)
		  (incf new-nc-2)))))
	  (values (first pivots) last-piv new-nc))))))

;;; ------------------------------------------------------------

(defun run-modular-hnf (in-file m n)
  "The file named in-file holds zero or more sparse-v's which are
the columns of an m-by-n csparse.  This function returns the name
of a file which holds the Hermite normal form of the csparse.
  Here's an outline of the method:
Let p0 be a five-digit prime, e.g. 31991.
Reduce the csparse mod p0 to find a large square minor
of non-zero det.  Call the columns containing this minor
the 'strip'.  Put columns that aren't in the strip aside.
Permute rows in the strip so the minor is at the top.
The key step: find the det of the minor [which is non-zero in Z
because it was non-zero mod p0], and find the HNF
of the minor by working modulo the det throughout.
For a sequence of primes p, do the following.
Put the strip into modified echelon form mod p, taking care to make
the echelon form match the HNF in the top square.  [E.g., if
the HNF over Z is
 1  0
34 89
and p = 3, then we reduce the strip mod 3 so the top is
 1  0
 1 -1
mod 3.]  Use the Chinese remainder theorem, combining
the reduction for this p with all previous p's, and make
a Z-matrix with the absolutely-least residues of everything.
This is the 'candidate HNF' of the strip.  To test if
the candidate HNF is correct, run through every vector
in in-file and see if it reduces over Z to zero modulo
the columns of the candidate."
  (declare (type nnfixnum m n))
  (multiple-value-bind (strip non-strip pivot-rows)
      (indep-strip-mod in-file m n 31991)
    (declare (ignore strip non-strip pivot-rows)) ;; till it's written
    (error "WRITE ME.")))

(defun indep-strip-mod (in-file m n p0)
  "The file named in-file holds zero or more sparse-v's which are
the columns of an m-by-n csparse.
Let p0 be a five-digit prime, e.g. 31991.
Reduce the csparse mod p0 to find a large square minor
of non-zero det.  Call the columns containing this minor
the 'strip', and put them into a file called strip-file.
Put the other columns into a file called non-strip-file.
Return three values: strip-file, non-strip-file,
and pivot-rows, which is an increasing list of row indices.
Pivot-rows means that the large square minor resides in
the indicated rows of the strip.  [The number of columns
in the strip is the length pivot-rows.]"
  ;; 9/27/06: Keep the whole echelon form in memory.  (Fatal, at least
  ;; we start at corner = 0?)  Construct it with hnf-lower-tri.  Read
  ;; in the sparse-v's v one by one from in-file.  Remember v over D,
  ;; and also create a copy v0 reduced mod p0.  Merge v0 into the list
  ;; vv of currently reduced columns and run hnf-lower-tri.  Use the
  ;; second value to keep track of whether vv got longer; depending on
  ;; that, write v to strip-file or non-strip-file.  At the end, do a
  ;; simple mapcar to get pivot-rows.
  (declare (ignore in-file m n p0)) ;; till it's written
  (error "WRITE ME."))

;;; ==================== Restricted to Euclidean D ====================

(defmethod make-snf ((mat csparse) &optional (use-p t) (use-q t) (destructive-p nil) (p-q-to-file nil))
  "Returns the Smith normal form of mat, a csparse over the integral
domain D, while aiming to avoid fill-in and entry explosion.
  The Smith normal form is
        mat = p d q.
The matrix d, held as a csparse in an snf's slot d, is a
diagonal matrix
        d = diag(d0, d1, d2, ...),
over D.  Here d0 is a divisor of d1, d1 is a divisor of d2, and so on
for all dj and d(j+1).  If dk is zero, then so are d(k+1), d(k+2), etc.
The dj's are called the elementary divisors.
  p and q are square matrices over Z of determinant +/- 1 [hence
invertible over D].  They are represented by an snf's p-list and
q-list, which are lists of elementary matrices--instances of perm, perm2
and transv.  p is the product of the matrices in p-list, and q the product
for q-list, both in the usual left-to-right order.  The 'list' in
p-list and q-list is a figure of speech: the data may be stored in the
snf's slots p-list and q-list, or may be stored in files in the current
working directory.  The recommend way to read the p's in left-to-right
order is by do-snf-p, and in right-to-left order by do-snf-p-rev, and
similarly for the q's.  These do-snf-... macros hide the details of file
versus list.  If the p's and q's are stored on disk, the files have
these names [where NN is an integer]:
snfpNN.txt ... p's in left-to-right order
snfqNN.txt ... q's in left-to-right order
snfbNN.txt ... p's in right-to-left order [b = voiced p sound]
snfhNN.txt ... q's in right-to-left order [h = unvoiced q sound]
snfdNN.txt ... the csparse d, or see make-snf-from-disk.
  The optional arguments to make-snf can save space with large csparses.
If use-p is nil, the matrices in p-list are not computed.  Ditto for
use-q and q-list.  By default, use-p and use-q are true.  If
destructive-p is nil, the default, the original matrix is preserved in
mat, and the reduction steps work on a copy; if destructive-p is true,
the original matrix is destroyed during the reduction.  If p-q-to-file
is true, the p's and q's are written to files; if it's nil, the
default, they are stored in RAM.
  make-snf fires the Smith normal form computation automatically.  The
algorithm is in the function jac and the various pivot functions it
calls.
  By changing the following variables, the user can specify different
forms of the algorithm.  Please see the documentation for details.
*allow-markowitz*
*allow-block-tri*
*allow-minor-trick* *minor-trick-threshold* *minor-trick-col-func*
*allow-wiedemann-winnow* *wiedemann-winnow-threshold*
*allow-disk-hnf* *disk-hnf-threshold* *disk-hnf-width*
[if D = Z] *allow-lll* *lll-width* *lll-threshold* *lll-next-try*
[being written] *allow-modular-hnf* *modular-hnf-threshold*
  Use the following flags to view graphs and windows that show the
progress of the computation.
*verbose* *show-stats* *show-csw*"
  (jac (make-instance 'snf
	 :mat (if destructive-p nil mat)
	 :d (if destructive-p mat (csparse-copy mat))
	 :use-p use-p
	 :use-q use-q
	 :p-q-to-file p-q-to-file
	 :file-counter (if p-q-to-file (new-file-counter) -1))))

(defun jac (a)
  "The main algorithm for Smith normal form computations.  Fills out
the slots of the snf a and returns A.  The author calls this method
jac because he learned it as Theorem 3.8 of the book Basic Algebra I
by Nathan Jacobson."
  (declare (type snf a))
  (with-slots (d use-p use-q p-q-to-file (fc file-counter) p-list q-list) a
    (declare (type csparse d) (list p-list q-list))
    (with-csparse-slots (m n cols) d
      (let ((dim (min m n))
	    (corner 0)
	    (show-prog-mod (max 1 (min (ceiling n 20)
				       (if *allow-lll* *lll-next-try* 1000000)
				       100)))
	    (piv-i 0)
	    (piv-j 0)
	    (piv-v nil) ;; sparse-elt or nil
	    (last-lll (- *lll-next-try*))
	    (block-tri-has-run nil)
	    (wiedemann-winnow-has-run nil)
	    (disk-hnf-has-run nil)
	    (modular-hnf-has-run nil)
	    (spar-stats nil)
	    (p-stats nil)
	    (q-stats nil)
	    (csw-delta 1)
	    (csw-width 0)
	    (csw-height 0)
	    (csw-counter nil)
	    (*inside-field-p* (aand (first (some #'identity cols))
				    (sp-field-p it)))
	    (*inside-f_p-p* (aand (first (some #'identity cols))
				  (sp-f_p-p it))))
	(declare (type nnfixnum dim corner show-prog-mod piv-i piv-j
		       csw-delta csw-width csw-height)
		 (fixnum last-lll)
		 (type (or simple-vector null) spar-stats p-stats q-stats))
	(labels ((update-stats (p-q-changed)
		   (when (or *show-csw* (and *show-stats* p-q-changed))
		     (let ((spars (* 100 (sparsity d corner))))
		       (when (and *show-stats* p-q-changed)
			 (setf (svref spar-stats corner) spars)
			 (when p-stats
			   (setf (svref p-stats corner) (length p-list)))
			 (when q-stats
			   (setf (svref q-stats corner) (length q-list))))
		       (when *show-csw*
			 (csw-set-note
			  (format nil "Pivot ~D.  Sparsity ~,1F%." corner spars))))))
		 (paint-matrix ()
		   (when *show-csw*
		     (csw-set-corner corner)
		     (when (csw-is-active)
		       (to-counter d csw-delta csw-width csw-height csw-counter)
		       (csw-set-counter csw-counter))))
		 (d-diagonal-p ()
		   (dotimes-f (j n t)
		     (unless (endp (svref cols j))
		       (if (< j m)
			   (unless (and (endp (rest (svref cols j)))
					(= j (sp-i (first (svref cols j)))))
			     (return nil))
			 (return nil))))))
	  (with-open-file (p-out-stream
			   (if (and p-q-to-file use-p)
			       (format nil "snfp~D.txt" fc)
			     "wontBeWritten.txt")
			   :direction :output
			   :if-exists (if (and p-q-to-file use-p)
					  :supersede
					nil)
			   :if-does-not-exist (if (and p-q-to-file use-p)
						  :create
						nil))
	    (with-open-file (q-rev-out-stream
			     (if (and p-q-to-file use-q)
				 (format nil "snfh~D.txt" fc)
			       "wontBeWritten.txt")
			     :direction :output
			     :if-exists (if (and p-q-to-file use-q)
					    :supersede
					  nil)
			     :if-does-not-exist (if (and p-q-to-file use-q)
						    :create
						  nil))
	      (prog ()
		(when *verbose*
		  (format t "~&Starting jac on a ~D by ~D matrix" m n)
		  (when p-q-to-file
		    (format t ", fc ~D," fc))
		  (format t " ~A~&~A~&" (time-stamp) (pivot-method)))
		(unless (zerop dim)
		  (when *show-stats*
		    (let ((d1 (1+ dim)))
		      (setq spar-stats (make-array d1 :initial-element 0))
		      (when (and use-p (not p-q-to-file))
			(setq p-stats (make-array d1 :initial-element 0)))
		      (when (and use-q (not p-q-to-file))
			(setq q-stats (make-array d1 :initial-element 0)))))
		  (when *show-csw*
		    (multiple-value-bind (delta w h) (csw-init (pivot-method) m n)
		      (declare (type nnfixnum delta w h))
		      (setq csw-delta delta csw-width w csw-height h
			    csw-counter (make-array (* w h) :element-type '(signed-byte 32)))))
		  (paint-matrix))
	       step1
		;; Get a new pivot.  But first, if we're not storing
		;; the q's, run whatever big column-operation tricks
		;; that have been turned on.  These include LLL, the
		;; minor trick, disk HNF, and modular HNF.
		(when (and *verbose* (zerop (mod corner show-prog-mod)))
		  (format t "~&    ~D ~5,3F ~A~&"
			  corner (sparsity d corner) (time-stamp)))
		(update-stats nil)
		;; Block-triangularize and recursively reduce, if appropriate.
		(when (and *allow-block-tri* (not block-tri-has-run)
			   (not use-q) (zerop corner) (> m 1) (> n 1))
		  ;; "block" block of July 2-18, 2006 and Summer 2007
		  (setq block-tri-has-run t)
		  (till (d-diagonal-p)
		    (when *verbose*
		      (format t "~&Starting ~D by ~D block-tri ~A" m n (time-stamp)))
		    (multiple-value-bind (size-list bt-P bt-Q) (block-triangularize-2 d #'(lambda () (paint-matrix)))
		      (declare (list size-list) (type perm bt-P) (ignore bt-Q))
		      (when *verbose*
			(format t "~&Calculated block-tri ~A" (time-stamp)))
		      (if p-q-to-file
			  (format-flat p-out-stream "~S" bt-P)
			(push bt-P p-list)) ;; will nreverse at end
		      (update-stats t)
		      (paint-matrix)
		      (let ((num-blocks (length size-list)))
			(declare (type nnfixnum num-blocks))
			(when *verbose*
			  (format t "~&Before jac on ~D by ~D, have ~D triangular block~:P whose sizes [omitting 1's] are~&~A"
				  m n num-blocks (remove 1 size-list)))
			(let ((max-block-size 0)
			      (length-thru-max 1)) ;; an index in 'sizes'
			  (declare (type nnfixnum max-block-size length-thru-max))
			  (do ((size-tail size-list (rest size-tail))
			       (pos 0 (1+ pos)) ;; index in 'sizes'
			       (i 0)) ;; running sum of 'sizes'
			      ((endp size-tail))
			    (declare (list size-tail) (type nnfixnum pos i))
			    (let ((size (first size-tail)))
			      (declare (type nnfixnum size))
			      (when (> size max-block-size)
				(setq max-block-size size
				      length-thru-max (1+ pos)))
			      (when (= size 1)
				;; Try to wipe out the row to the
				;; right of entry i,i.
				(let ((col-i (svref cols i)))
				  (declare (type sparse-v col-i))
				  (when (v-singleton-p col-i)
				    (let ((e-ii (first col-i)))
				      (when (= (sp-i e-ii) i)
					(do ((j (1+ i) (1+ j)))
					    ((>= j n))
					  (declare (type nnfixnum j))
					  (with-splicer (svref cols j)
					    (till (or (splicer-endp) (> (sp-i (splicer-read)) i))
					      (if (= (sp-i (splicer-read)) i)
						  (if (sp-divides e-ii (splicer-read))
						      (splicer-delete)
						    (let ((r (sp-rounded-rem (splicer-read) e-ii)))
						      (assert (not (sp-zerop r)) () "sp-rounded-rem error.")
						      (splicer-modify r)
						      (splicer-fwd)))
						(splicer-fwd)))))
					(update-stats nil))))))
			      (incf i size)))
			  (let* ((scc-profile (subseq size-list 0 length-thru-max))
				 (n1 (apply #'+ scc-profile)))
			    (declare (list scc-profile) (type nnfixnum n1))
			    (let ((m1 0))
			      (declare (type nnfixnum m1))
			      (dotimes-f (j n1)
				(when (svref cols j)
				  (maxf m1 (1+ (sp-i (first (last (svref cols j))))))))
			      (when (<= m n)
				(unless (= m1 n1)
				  (cerror "Keep going anyway."
					  "In a ~D by ~D, in leftmost cols < ~D after block-tri,~&  effective m is ~D instead of square." m n n1 m1)))
			      (when *show-csw*
				(csw-set-yellow 0 n1))
			      (let ((d1 (make-csparse-zero m1 n1))
				    (*allow-block-tri* nil)
				    (*show-csw* nil))
				(dotimes-f (j n1)
				  (setf (svref (csparse-cols d1) j) (svref cols j)
					(svref cols j) '()))
				(reset-markowitz d1)
				(when *verbose*
				  (format t "~&Running sub-jac before main jac on~&block-triangular strips of these widths:~&~A" scc-profile))
				(let ((snf1 (make-snf d1 t nil t p-q-to-file)))
				  (when *verbose*
				    (format t "~&Sub-jac's snf1 = ~A" snf1))
				  (let ((oo (make-csparse-zero m 1))
					(p1-inv-list '())
					(nu1 (num-units snf1))
					(j-to-modulus (make-hash-table :size (length (torsion snf1)))))
				    (declare (list p1-inv-list) (type nnfixnum nu1) (hash-table j-to-modulus))
				    (when *verbose*
				      (format t "~&Number of sub-jac P's in RAM:"))
				    (let ((p1-ct 0))
				      (declare (type nnfixnum p1-ct))
				      (do-snf-p (p1 snf1)
					(push (m-inverse p1) p1-inv-list)
					(incf p1-ct)
					(multiple-value-bind (q r) (floor p1-ct 1000)
					  (declare (type nnfixnum q r))
					  (when (and *verbose* (zerop r))
					    (format t " ~DK" q))))
				      (when *verbose*
					(format t " total ~D" p1-ct)))
				    (setq p1-inv-list (nreverse p1-inv-list))
				    (do ((j1 nu1 (1+ j1))
					 (tail (torsion snf1) (rest tail)))
					((endp tail))
				      (declare (type nnfixnum j1))
				      (puthash j1 (first tail) j-to-modulus))
				    (dotimes-f (j n)
				      (when (and *verbose* (zerop (mod j 100)))
					(format t "~&    oo ~D" j))
				      (let ((v (svref cols j)))
					(declare (type sparse-v v))
					(when v
					  (assert (>= j n1) ())
					  (setf (svref (csparse-cols oo) 0) v)
					  (dolist (p1 p1-inv-list)
					    (m-mult p1 oo))
					  (setq v (svref (csparse-cols oo) 0))
					  (till (or (endp v) (>= (sp-i (first v)) nu1))
					    (pop v))
					  (with-splicer v
					    (till (or (splicer-endp)
						      (not (has-key
							    (sp-i (splicer-read))
							    j-to-modulus)))
					      (let ((r (sp-rounded-rem
							(splicer-read)
							(gethash
							 (sp-i (splicer-read))
							 j-to-modulus))))
						(if (sp-zerop r)
						    (splicer-delete)
						  (progn
						    (splicer-modify r)
						    (splicer-fwd))))))
					  (setf (svref cols j) v)))))
				  (dotimes-f (j1 n1)
				    (setf (svref cols j1)
				      (svref (csparse-cols (slot-value snf1 'd)) j1)))
				  (reset-markowitz d)
				  (do-snf-p (p1 snf1)
				    (if p-q-to-file
					(format-flat p-out-stream "~S" p1)
				      (push p1 p-list))) ;; will nreverse at end
				  (update-stats t)))
			      (when *show-csw*
				(csw-set-yellow n n))
			      (paint-matrix))))))))
		;; Reduce by LLL if appropriate.
		(when (and *allow-lll* (not use-q)
			   (>= corner (+ last-lll *lll-next-try*))
			   (> (sparsity d corner) *lll-threshold*))
		  (hit-with-lll d corner)
		  (when (< last-lll 0)
		    (hit-with-lll d corner)) ;; twice the first time
		  (setq last-lll corner))
		;; Reduce by minor trick if appropriate.
		(when (and *allow-minor-trick* (not use-q) p-q-to-file
			   (< (funcall *minor-trick-col-func* (- m corner))
			      (- n corner))
			   (> (sparsity d corner) *minor-trick-threshold*))
		  (high-rank-light-front-minor d corner)
		  (let ((mf (make-multi-file
			     :stem (minor-trick-stem (new-file-counter)))))
		    (do ((j corner (1+ j)))
			((= j n))
		      (declare (type nnfixnum j))
		      (when (svref cols j)
			(multi-file-print
			 (mapcar
			  #'(lambda (e)
			      ;; See next GASP!
			      (copy-sp e (- (sp-i e) corner)))
			  (svref cols j))
			 mf)
			(setf (svref cols j) '())))
		    (multi-file-lock mf)
		    ;; Rest is GASP! DUPLICATION! code copied from
		    ;; do-minor-trick.
		    (let ((snf1 (do-minor-trick (- m corner) (- n corner) mf use-p)))
		      (multi-file-delete mf)
		      (let ((j corner)
			    (j1 0))
			(declare (type nnfixnum j j1))
			(with-csparse-slots ((m1 m) (n1 n) (c-d1 cols)) (slot-value snf1 'd)
			  (till (or (= j1 m1) (= j1 n1)
				    (v-zerop (svref c-d1 j1)))
			    ;; Take out the next two asserts after testing.
			    (assert (endp (rest (svref c-d1 j1))) ()
			      "c-d1 not diag (2).")
			    (assert (= j1 (sp-i (first (svref c-d1 j1)))) ()
			      "d1 has an off-diagonal entry.")
			    (csparse-set d
					 (copy-sp (first (svref c-d1 j1))
						  j)
					 j)
			    (incf j)
			    (incf j1))))
		      (reset-markowitz d)
		      (when use-p
			(do-snf-p (p snf1)
			  (format-flat p-out-stream "~S"
				       (m-translate p corner))))
		      (setq corner dim)
		      (when *verbose*
			(format t "~&Done pasting minor trick into jac ~A~&"
				(time-stamp))))))
		;; Reduce by wiedemann-winnow if appropriate.
		(when (and *allow-wiedemann-winnow* (not use-q)
			   (not wiedemann-winnow-has-run)
			   (> (sparsity d corner)
			      *wiedemann-winnow-threshold*))
		  (wiedemann-winnow d corner)
		  (setq wiedemann-winnow-has-run t))
		;; Reduce by disk-hnf if appropriate.
		(when (and *allow-disk-hnf* (not disk-hnf-has-run) (not use-q)
			   (> (sparsity d corner) *disk-hnf-threshold*))
		  (hit-with-disk-hnf d :i0 corner :start corner)
		  (setq disk-hnf-has-run t))
		;; Reduce by modular HNF if appropriate.
		(when (and *allow-modular-hnf*
			   (not *inside-field-p*)
			   (not modular-hnf-has-run)
			   (not use-q)
			   (funcall *modular-hnf-threshold*
				    m n corner (sparsity d corner)))
		  (let ((dense-file (new-disk-hnf-filename)))
		    (with-open-file (so dense-file :direction :output)
		      (do ((j corner (1+ j)))
			  ((= j n))
			(declare (type nnfixnum j))
			(when (svref cols j)
			  (format-flat
			   so "~S"
			   (mapcar #'(lambda (e)
				       (copy-sp e (- (sp-i e) corner)))
				   (svref cols j)))
			  (setf (svref cols j) '()))))
		    (let ((out-file (run-modular-hnf
				     dense-file (- m corner) (- n corner)))
			  (j corner))
		      (declare (type nnfixnum j))
		      (delete-file dense-file)
		      (with-open-file (si out-file)
			(awhile (read si nil)
			  (setf (svref cols j)
			    (mapcar #'(lambda (e)
					(copy-sp e (+ (sp-i e) corner)))
				    (the sparse-v it)))
			  (incf j)))
		      (delete-file out-file)))
		  (reset-markowitz d)
		  (setq modular-hnf-has-run t))
		;; Get pivot.
		(multiple-value-bind (pi0 pj0 pv0) (pivot d corner use-q last-lll)
		  (setq piv-i pi0 piv-j pj0 piv-v pv0))
		(unless piv-v ;; d is all 0 in southeast region
		  (go end))
		;; Permute the pivot to (corner,corner) position.
		(unless (= corner piv-j)
		  (swap-cols d corner piv-j)
		  (when use-q
		    (let ((elem (make-perm2 corner piv-j)))
		      (if p-q-to-file
			  (format-flat q-rev-out-stream "~S" elem)
			(push elem q-list)))))
		(unless (= corner piv-i)
		  (swap-rows d corner piv-i)
		  (when use-p
		    (let ((elem (make-perm2 corner piv-i)))
		      (if p-q-to-file
			  (format-flat p-out-stream "~S" elem)
			(push elem p-list))))) ;; will nreverse at end
		(go step3)
	       step2 ;; Increment corner.
		(update-stats t)
		(incf corner)
		(paint-matrix)
		(setq piv-v nil)
		(if (< corner dim)
		    (go step1)
		  (go end))
	       step3 ;; Main step: try to clear the corner-th row and column.
		(update-stats nil)
		;; Try to clear the corner-th row.
		(do ((j (1+ corner) (1+ j)))
		    ((= j n))
		  (declare (type nnfixnum j))
		  (let ((dcj (csparse-get d corner j)))
		    (when dcj
		      (if (and nil ;; see break 6 lines below
                               (not use-q) ;; [++?++]
			       (not (sp-divides piv-v dcj))
			       (sp-z-p piv-v))
			  (multiple-value-bind (hen ri) (disk-hnf-2-col-step (svref cols corner) (svref cols j))
			    (declare (type sparse-v hen ri))
			    (break
"When jac uses disk-hnf-2-col-step, we haven't gotten around to
updating d's rlen and clen.  Either write that code, or replace
the 'and' clause marked [++?++] with nil.  You could write it
as a sweep down (svref cols corner) and hen simultaneously,
and another sweep down the other two.")
			    (setf (svref cols corner) hen
				  (svref cols j) ri
				  ;; 5/18/2006: do you reset piv-v
				  ;; and keep going, or go to step1?
				  ;; Tests on 5/19 suggest it doesn't
				  ;; make one bit of difference!
				  piv-v (first hen)))
			(let ((quo (sp-neg-closest-quotient dcj piv-v)))
			  (unless (sp-zerop quo)
			    (alter-col d j quo corner)
			    (when use-q
			      (let ((elem (make-transv j (sp-negate quo corner))))
				(if p-q-to-file
				    (format-flat q-rev-out-stream "~S" elem)
				  (push elem q-list))))))))))
		(do ((j (1+ corner) (1+ j)))
		    ((= j n))
		  (declare (type nnfixnum j))
		  (when (and (not (endp (svref cols j)))
			     (= (sp-i (first (svref cols j))) corner))
		    (go step1)))
		;; Try to clear the corner-th column.
		(dolist (dic (copy-list (rest (svref cols corner))))
		  (let ((quo (sp-neg-closest-quotient dic piv-v)))
		    (unless (sp-zerop quo)
		      ;; Next form is equivalent to
		      ;; (alter-row d (sp-i dic) quo corner)
		      ;; but faster, because the corner-th row has exactly
		      ;; one non-zero entry, which is in the corner-th column.
		      (multiple-value-bind (ans census) (v-alter-elt (svref cols corner) (sp-i dic) quo corner)
			(setf (svref cols corner) ans)
			(update-census d corner census))
		      (when use-p
			(let ((elem (make-transv corner (sp-negate quo))))
			  (if p-q-to-file
			      (format-flat p-out-stream "~S" elem)
			    (push elem p-list))))))) ;; will nreverse at end
		;; Did they both get clear?
		(when (sp-unitp piv-v) ;; If pivot is invertible, got clear.
		  (go step2))
		(unless (endp (rest (svref cols corner)))
		  (go step1)) ;; corner-th col not clear.
		;; Is every other southeast entry divisible by the pivot?
		(do ((j (1+ corner) (1+ j)))
		    ((= j n))
		  (declare (type nnfixnum j))
		  (dolist (dij (svref cols j))
		    (unless (sp-divides piv-v dij)
		      ;; No, dij isn't.  Add 1 times the j-th col to the
		      ;; corner-th column, and go to step3.
		      (alter-col d corner (sp-embed-z piv-v 1) j)
		      (when use-q
			(let ((elem (make-transv corner
						 (sp-embed-z piv-v -1 j))))
			  (if p-q-to-file
			      (format-flat q-rev-out-stream "~S" elem)
			    (push elem q-list))))
		      (go step3))))
		;; Yes, everything got clear.
		(go step2)
	       end
		(return)))) ;; exit prog and two with-open-files
	  (update-stats t))
	(when p-q-to-file
	  (with-open-file (so (format nil "snfd~D.txt" fc)
			   :direction :output :if-exists :supersede)
	    ;; TO DO: if the "when" test fails, print d, sans print-object.
	    (when (and *inside-field-p* (not (and use-p use-q)))
	      (format so "~D ~D ~D ~S" m n (aif (position-if #'endp cols) it n) '()))))
	(when q-stats
	  (show-line-graph q-stats "New Q's"))
	(when p-stats
	  (show-line-graph p-stats "New P's"))
	(when spar-stats
	  (show-line-graph spar-stats "Sparsity (%)"))))
    (when (and (not p-q-to-file) use-p)
      (setf p-list (nreverse p-list))) ;; as promised above
    ;;(break "If you are Mark McConnell and~&are planning to paste snfp*.txt files together by~&hand, now is the time to quit and do it.")
    (when p-q-to-file
      (when *verbose*
	(format t "~&    Reversing P and Q files ~A~&" (time-stamp)))
      (when use-p
	(rev-lists (format nil "snfp~D.txt" fc) (format nil "snfb~D.txt" fc)))
      (when use-q
	(rev-lists (format nil "snfh~D.txt" fc) (format nil "snfq~D.txt" fc))))
    (when *verbose*
      (format t "~&    Ending jac ~A~&" (time-stamp)))
    a))

(defun make-snf-from-disk (fc &optional (make-sp #'make-sp-z))
  "If an snf has been precomputed and stored in disk files with
file-counter fc, this method reconstructs and returns the snf.
We use the P's iff a file snfp[fc].txt exists, and ditto for
the Q's and snfq[fc].txt.  The file snfd[fc].txt can have one of
two formats:
[.] d as a csparse structure.  In this case, make-sp is ignored.
[.] four items: m, n, num-units, and a list of torsion coefficients.
    We set d to an m by n diagonal matrix with the first 'num-units'
    entries 1 and succeeding entries from the torsion list.
    These sparse-elt entries are constructed from make-sp with
    value argument 1, respectively the items in the torsion list."
  (let (d)
    (with-open-file (si (format nil "snfd~D.txt" fc))
      (let ((item0 (read si nil)))
	(if (csparse-p item0)
	    (setq d item0)
	  (let* ((m item0)
		 (n (read si nil))
		 (nu (read si nil))
		 (tor (read si nil)))
	    (assert (and (integerp m) (integerp n) (integerp nu)
			 (<= 0 m most-positive-fixnum)
			 (<= 0 n most-positive-fixnum)
			 (<= 0 nu most-positive-fixnum)) ()
	      "m, n and nu in snfd~D.txt must be non-neg fixnums." fc)
	    (assert (<= 0 (+ nu (length tor)) (min m n)) ()
	      "nu and tor are too big in snfd~D.txt." fc)
	    (setq d (make-csparse-zero m n))
	    (dotimes-f (i nu)
	      (csparse-set d (funcall make-sp i 1) i))
	    (do ((i nu (1+ i))
		 (tail tor (rest tail)))
		((endp tail))
	      (csparse-set d (funcall make-sp i (first tail)) i))))))
    (make-instance 'snf
      :mat nil :d d :p-q-to-file t :file-counter fc
      :use-p (probe-file (format nil "snfp~D.txt" fc))
      :use-q (probe-file (format nil "snfq~D.txt" fc)))))

(defun pivot-greedy (cols corner)
  "A greedy implementation of 'pivot'.  Among sparse-elts of minimal
Euclidean norm in columns j >= corner, finds the first one in
column-major order."
  (declare (simple-vector cols) (type nnfixnum corner))
  (let ((n (length cols))
        (best-i 0)
        (best-j 0)
        (best-elt nil)
        (best-euc nil))
    (declare (type nnfixnum n best-i best-j))
    (do ((j corner (1+ j)))
        ((= j n) (values best-i best-j best-elt))
      (declare (type nnfixnum j))
      (dolist (e (svref cols j))
	(if *inside-field-p*
	    (return-from pivot-greedy (values (sp-i e) j e))
	  (let ((euc (sp-euc-norm e)))
	    (declare (integer euc))
	    (if (= euc 1)
		(return-from pivot-greedy (values (sp-i e) j e))
	      (when (or (null best-elt) (< euc (the integer best-euc)))
		(setq best-i (sp-i e) best-j j best-elt e best-euc euc)))))))))

(defun pivot-markowitz (d corner)
  "A pure Markowitz algorithm for pivoting."
  (declare (type nnfixnum corner))
  (with-csparse-slots (n cols rlen clen) d
    ;; Main sweep: get best pivot.
    (let ((best-i 0)
	  (best-j 0)
	  (best-elt nil)
	  (best-markow-ct nil))
      (block main-loop
	(if *inside-field-p*
	    (do ((j corner (1+ j))) ;; specialize next do loop w/o norm
		((>= j n))
	      (declare (type nnfixnum j))
	      (let ((clen-j (svref clen j)))
		(dolist (ae (the sparse-v (svref cols j)))
		  (let ((markow-ct (* (the nnfixnum (svref rlen (sp-i ae)))
				      (the nnfixnum clen-j))))
		    (declare (integer markow-ct))
		    (when (or (null best-elt)
			      (< markow-ct (the integer best-markow-ct)))
		      (setq best-i (sp-i ae) best-j j best-elt ae
			    best-markow-ct markow-ct)
		      (when (zerop markow-ct)
			(return-from main-loop)))))))
	  (let ((best-norm nil))
	    (do ((j corner (1+ j)))
		((>= j n))
	      (declare (type nnfixnum j))
	      (let ((clen-j (svref clen j)))
		(dolist (ae (the sparse-v (svref cols j)))
		  (let ((norm (sp-euc-norm ae))
			(markow-ct (* (the nnfixnum (svref rlen (sp-i ae)))
				      (the nnfixnum clen-j))))
		    (declare (integer norm markow-ct))
		    (when (or (null best-elt)
			      (< norm (the integer best-norm))
			      (and (= norm (the integer best-norm))
				   (< markow-ct (the integer best-markow-ct))))
		      (setq best-i (sp-i ae) best-j j best-elt ae
			    best-norm norm best-markow-ct markow-ct)))))))))
      (values best-i best-j best-elt))))

;;; -------------------- Minor Trick --------------------

;; Requires use-q = nil.
(defun do-minor-trick (m n mf use-p &optional (depth 0))
  "The multi-file mf holds non-zero sparse-v's that comprise
the non-zero columns of an m-by-n csparse.  Returns an snf holding
the reduction of the csparse."
  (declare (type nnfixnum m n depth))
  (if (or (zerop m) (zerop n))
      (return-from do-minor-trick
	(make-instance 'snf
	  :mat nil :d (make-csparse-zero m n) :use-p use-p :use-q nil
	  :p-q-to-file nil :file-counter -1))
    ;; Let mat0 be the largest left-hand strip of mat [the original
    ;; matrix] that we think we can reduce using a csparse that's
    ;; close to 100% dense.  The width of mat0 is n0.
    (let* ((n0 (min (max (funcall *minor-trick-col-func* m) 1) n))
	   (mat0 (make-csparse-zero m n0))
	   (sample-elt nil)
	   (sample-elt-char nil))
      (declare (type nnfixnum n0))
      (when *verbose*
	(format t "~&Starting minor trick, depth ~D, on a ~D by ~D matrix ~A~&"
		depth m n0 (time-stamp)))
	;; Fill mat0 with the first n0 columns.
	(with-csparse-slots ((cols0 cols)) mat0
	  (multi-file-init-read mf)
	  (do ((j 0 (1+ j))
	       (v (multi-file-read mf) (multi-file-read mf)))
	      ((or (= j n0) (null v)))
	    (declare (type nnfixnum j))
	    (setf (svref cols0 j) v)
	    (unless sample-elt
	      (setq sample-elt (first v))
	      (aif (sp-f_p-p sample-elt)
		   (setq sample-elt-char it)
		(when (sp-z-p sample-elt)
		  (setq sample-elt-char 0)))))
	  (reset-markowitz mat0))
	;; Is mat0 already in SNF, while the file has no more columns?
	(when (and (null (multi-file-peek mf))
		   (snf-diagonal-p mat0))
	  (return-from do-minor-trick
	    (make-instance 'snf
	      :mat nil :d mat0 :use-p use-p :use-q nil
	      :p-q-to-file nil :file-counter -1)))
	;; sample-elt can't be null because n0 >=1 and, after the last
	;; clause, we know the v's hadn't run out.
	(assert sample-elt () "Minor trick sample-elt is null.")
	;; Find SNF of mat0, remembering their P0's and D0.  nu0 is
	;; the horizontal cut-off line above which D0 has only 1's.
	(let* ((snf0 (make-snf mat0 t nil t t))
	       (nu0 (num-units snf0))
	       (mf0 (make-multi-file
		     :stem (minor-trick-stem (slot-value snf0 'file-counter)))))
	  (declare (type nnfixnum nu0))
	  (when *verbose*
	    (format t "~&Minor trick: depth ~D minor has nu0 = ~D, torsion ~S.~&" depth nu0 (mapcar #'sp-print-value (mapcar #'sp-pretty-associate (torsion snf0)))))
	  ;; Write out a new file with [i] any cols of D0 beyond the
	  ;; first nu0, as well as [ii] P0-translates of all the
	  ;; remaining cols of mat.  We chop off the top nu0 rows of
	  ;; [ii], using col operations with the 1's of D0; when we
	  ;; write the answers out, the row-indices are decremented by
	  ;; nu0.
	  (block fill-file0
	    (labels ((nu0-decr (e)
		       (copy-sp e (- (sp-i e) nu0))))
	      (with-csparse-slots ((c-d0 cols)) (slot-value snf0 'd)
		(do ((j nu0 (1+ j)))
		    ((or (= j n0) (v-zerop (svref c-d0 j))))
		  (declare (type nnfixnum j))
		  (multi-file-print (mapcar #'nu0-decr (svref c-d0 j)) mf0)))
	      (let ((oo (if sample-elt-char
			    (make-array m)
			  (make-csparse-zero m 1)))
		    (j-to-modulus
		     (make-hash-table
		      :size (length (torsion snf0)))))
		(do ((j0 nu0 (1+ j0))
		     (tail (torsion snf0) (rest tail)))
		    ((endp tail))
		  (declare (type nnfixnum j0))
		  (puthash j0 (first tail) j-to-modulus))
		(loop
		  (let ((v (multi-file-read mf)))
		    (declare (type sparse-v v))
		    (unless v
		      (return-from fill-file0))
		    (cond (sample-elt-char
			   (fill oo 0)
			   (dolist (e v)
			     (setf (svref oo (sp-i e)) (sp-integer-lift e)))
			   (do-snf-p (p0 snf0)
			     (elem-times-vector (m-inverse p0) oo))
			   (setq v '())
			   (do ((i (1- m) (1- i)))
			       ((< i 0))
			     (declare (fixnum i))
			     (let ((val (svref oo i)))
			       (declare (integer val))
			       (unless (zerop val)
				 (push (sp-embed-z sample-elt val i) v)))))
			  (t
			   (setf (svref (csparse-cols oo) 0) v)
			   (reset-markowitz oo)
			   (do-snf-p (p0 snf0)
			     (m-mult (m-inverse p0) oo))
			   (setq v (svref (csparse-cols oo) 0))))
		    (till (or (endp v) (>= (sp-i (first v)) nu0))
		      (pop v))
		    (with-splicer v
		      (till (or (splicer-endp)
				(not (has-key
				      (sp-i (splicer-read))
				      j-to-modulus)))
			(let ((r (sp-rounded-rem
				  (splicer-read)
				  (gethash
				   (sp-i (splicer-read))
				   j-to-modulus))))
			  (if (sp-zerop r)
			      (splicer-delete)
			    (progn
			      (splicer-modify r)
			      (splicer-fwd))))))
		    (when v
		      (multi-file-print (mapcar #'nu0-decr v) mf0)))))))
	  (multi-file-lock mf0)
	  ;; Find the SNF of what's in the new file, remembering its
	  ;; P1's and D1.
	  (let ((snf1 (do-minor-trick (- m nu0) (- n nu0) mf0 use-p (1+ depth)))
		(ans-d (make-csparse-zero m n))
		(ans-fc (new-file-counter)))
	    (multi-file-delete mf0)
	    (let ((j 0))
	      (declare (type nnfixnum j))
	      (with-csparse-slots ((c-d0 cols)) (slot-value snf0 'd)
		(till (= j nu0)
		  ;; Take out the next four asserts after some testing.
		  (assert (not (endp (svref c-d0 j))) ()
		    "c-d0 not diag (0).")
		  (assert (endp (rest (svref c-d0 j))) ()
		    "c-d0 not diag (2).")
		  (assert (= j (sp-i (first (svref c-d0 j)))) ()
		    "d0 has an off-diagonal entry.")
		  (assert (sp-unitp (first (svref c-d0 j))) ()
		    "d0 has a non-unit before nu0.")
		  (csparse-set ans-d (first (svref c-d0 j)) j)
		  (incf j)))
	      (let ((j1 0))
		(declare (type nnfixnum j1))
		(with-csparse-slots ((m1 m) (n1 n) (c-d1 cols))
		                    (slot-value snf1 'd)
		  (till (or (= j1 m1) (= j1 n1) (v-zerop (svref c-d1 j1)))
		    ;; Take out the next two asserts after some testing.
		    (assert (endp (rest (svref c-d1 j1))) ()
		      "c-d1 not diag (2).")
		    (assert (= j1 (sp-i (first (svref c-d1 j1)))) ()
		      "d1 has an off-diagonal entry.")
		    (csparse-set ans-d
				 (copy-sp (first (svref c-d1 j1)) j)
				 j)
		    (incf j)
		    (incf j1)))))
	    (reset-markowitz ans-d)
	    (when use-p
	      (with-open-file (sp (format nil "snfp~D.txt" ans-fc)
			       :direction :output :if-exists :supersede)
		(do-snf-p (p snf0)
		  (format-flat sp "~S" p))
		(do-snf-p (p snf1)
		  (format-flat sp "~S" (m-translate p nu0)))))
	    (when *verbose*
	      (format t "~&Ending minor trick, depth ~D ~A~&"
		      depth (time-stamp)))
	    (make-instance 'snf
	      :mat nil :d ans-d :use-p use-p :use-q nil
	      :p-q-to-file t :file-counter ans-fc))))))

;;; --------------- Euclidean parts of disk-hnf ---------------

(defun disk-hnf-compare (v1 v2)
  "Compares by < on index of first entry, breaking ties by < on
Euclidean norm and then < on length.  Null sparse-vs go at the right
so result will be lower-triangular."
  (declare (type sparse-v v1 v2))
  (if (endp v1)
      nil ;; either () > non-null, or () = ()
    (if (endp v2)
	t ;; non-null < ()
      (let ((i1 (sp-i (first v1)))
	    (i2 (sp-i (first v2))))
	(declare (type nnfixnum i1 i2))
	(if (< i1 i2)
	    t
	  (if (> i1 i2)
	      nil
	    (let ((euc1 (sp-euc-norm (first v1)))
		  (euc2 (sp-euc-norm (first v2))))
	      (declare (integer euc1 euc2))
	      (if (< euc1 euc2)
		  t
		(if (> euc1 euc2)
		    nil
		  (do ((l1 v1 (rest l1))
		       (l2 v2 (rest l2)))
		    ((or (endp l1) (endp l2))
		     (not (endp l2))) ;; len v1 < len v2
		    (declare (type sparse-v l1 l2))))))))))))

(defun disk-hnf-clean (dhc1 lt2 &optional (sort-at-end t))
  "dhc1 and lt2 are dhc files.  The columns of lt2 should be strictly
lower-triangular.  We row-reduce every entry of dhc1 by every entry
in lt2.  At the end, dhc1 holds the reduced version of what it started
with, and lt2 is unchanged.
  Returns true iff some change in dhc1 was made.
  Usually we have to sort the result by disk-hnf-compare after
the row reduction.  If there is some special reason why we don't,
pass in nil for sort-at-end.
  See hit-with-disk-hnf for documentation on 'dhc'."
  (when *verbose*
    (format t "~&    Cleaning ~A~&" (time-stamp)))
  (let ((tmp (new-disk-hnf-filename))
	(new-nc1 0)
	(changed nil))
    (with-open-file (so tmp :direction :output :if-exists :supersede)
      (with-open-file (si1 dhc1)
	(do-sparse-v-list-stream (vv si1)
	  (let* ((vv-vec (map 'vector #'identity vv))
		 (vv-n (length vv-vec))
		 (vv-done (make-array vv-n :initial-element '())))
	    (declare (simple-vector vv-vec vv-done) (type nnfixnum vv-n))
	    (setq vv '()) ;; gc-help
	    (with-open-file (si2 lt2)
	      (do-sparse-v-stream (w si2)
		(declare (type sparse-v w))
		(assert w () "An entry of lt2 is empty.")
		(let* ((ew (first w))
		       (iw (sp-i ew)))
		  (declare (type nnfixnum iw))
		  (dotimes-f (j vv-n)
		    (till (or (endp (the sparse-v (svref vv-vec j)))
			      (>= (sp-i (first (the sparse-v (svref vv-vec j)))) iw))
		      (push (pop (the sparse-v (svref vv-vec j)))
			    (the sparse-v (svref vv-done j))))
		    (let ((ev (v-get (the sparse-v (svref vv-vec j)) iw)))
		      (when ev
			(let ((q (sp-neg-closest-quotient ev ew)))
			  (unless (sp-zerop q)
			    (v-alter-f (the sparse-v (svref vv-vec j)) q w)
			    (unless changed
			      (setq changed t))))))))))
	    (dotimes-f (j vv-n)
	      (when (or (the sparse-v (svref vv-done j))
			(the sparse-v (svref vv-vec j)))
		(format-flat so "~S"
			     (nreconc (the sparse-v (svref vv-done j))
				      (the sparse-v (svref vv-vec j))))
		(setf (svref vv-done j) '() (svref vv-vec j) '()) ;; gc-help
		(incf new-nc1)))
	    (setq vv-vec nil vv-done nil))))) ;; gc-help
    (when (and changed sort-at-end)
      (disk-hnf-sort tmp new-nc1))
    (rename-file tmp dhc1)
    (values new-nc1 changed)))

(defun hnf-lower-tri (vv)
  (declare (list vv))
  "Input is a list of non-empty sparse-v's sorted by disk-hnf-compare.
Output has two values: [i] their HNF, still with v's non-empty and
sorted; [ii] the number of columns in the HNF, i.e., (length [i]).
The top-level structure of vv will be altered."
  (assert (notany #'endp vv) () "Columns must not be zero.")
  (assert (every #'(lambda (v1 v2)
		     (declare (type sparse-v v1 v2))
		     ;; Test used to be "not > under
		     ;; disk-hnf-compare", but it sometimes failed.
		     ;; False positive?
		     (<= (sp-i (first v1)) (sp-i (first v2))))
		 vv (rest vv)) ()
    "Input was not sorted.")
  (let ((v-done '())
	(v-done-len 0)
	(ct 0)) ;; only for *verbose* messages
    (declare (list v-done) (type nnfixnum v-done-len) (fixnum ct))
    (till (endp vv)
      (let ((v (first vv)))
	(declare (type sparse-v v))
	(let ((i (sp-i (first v))))
	  (declare (type nnfixnum i))
	  (when (and *verbose* (zerop (mod ct 100)))
	    (format t "~&    hnf-lower-tri ct=~D i=~D ~A~&" ct i (time-stamp)))
	  (incf ct)
	  (if (or (endp (rest vv))
		  (> (sp-i (first (second vv))) i)) ;; w = (second vv)
	      (progn
		(let ((ve (first v)))
		  (map-into v-done
			    #'(lambda (v1)
				(declare (type sparse-v v1))
				(let ((v1e (v-get v1 i)))
				  (if v1e
				      (v-alter v1 (sp-neg-closest-quotient v1e ve) v)
				    v1)))
			    v-done))
		(push (pop vv) v-done)
		(incf v-done-len))
	    (let ((w (second vv)))
	      (declare (type sparse-v w))
	      (multiple-value-bind (new-v new-w) (disk-hnf-2-col-step v w)
		(declare (type sparse-v new-v new-w))
		;; new-v's first entry is still at i; new-w's lower
		(setf (first vv) new-v)
		(setf (rest vv) (rest (rest vv))) ;; cut out w
		(when new-w
		  (setq vv
		    (merge 'list vv (list new-w) #'disk-hnf-compare)))
		(setq new-v '() new-w '())) ;; gc-help
	      (setq w '())))) ;; gc-help
	(setq v '()))) ;; gc-help
    (values (nreverse v-done) v-done-len)))

(defun disk-hnf-2-col-step (v w)
  "Assumes things its caller checked: v and w are both non-empty
and have the same first index i.  Performs an invertible transformation
on the two columns.  Returns two values, new-v whose first index
is still i, and new-w whose first index [if any] is greater."
  (declare (type sparse-v v w))
  (if (sp-z-p (first v))
      (disk-hnf-2-col-step-z v w)
    ;; Dopey Euclidean version so we can say we have it.
    (if (endp w) ;; possible in a recursive step
	(values v w)
      (let ((ev (first v))
	    (ew (first w)))
	(if (> (sp-i ew) (sp-i ev)) ;; false on pass 1, usual exit later
	    (values v w)
	  (if (> (the integer (sp-euc-norm ev))
		 (the integer (sp-euc-norm ew)))
	      (disk-hnf-2-col-step w v)
	    (let ((q (sp-neg-closest-quotient ew ev)))
	      (assert (not (sp-zerop q)) ()
		"Division ~A / ~A has quotient zero~&though denominator's norm is the smaller?" ew ev)
	      (let ((new-w (v-add-nondestr
			    w
			    (v-scalar-mult (copy-list v) q))))
		(disk-hnf-2-col-step v new-w)))))))))

;;; --------------- HNF for csparses over Z or fields ---------------

(defgeneric hnf (A &optional i0)
  (:documentation
   "Destructively puts A into upper-triangular Hermite normal form, working
from the bottom up.  Currently it is implemented when the domain D either
is Z or is a field, and may work for other pairs (A,D).  Stops when the
region of rows i >= i0 is in HNF.  At the end, we remove columns of zeroes.
The input A can have one of these types:
[1] a vector of sparse-v's.  This vector must be adjustable and have
    a fill-pointer.  The function destructively alters the vector
    to hold the result, and returns the altered vector.
[2] a csparse.  The function returns a new csparse, possibly
    with smaller n.  The original csparse is not altered.
Use hnf-f to rebind A to the result."))

(defmacro hnf-f (A &optional i0)
  "Evaluates hnf and rebinds the first argument to the result."
  `(setf ,A (hnf ,A ,@(if i0 (list i0) '()))))

(defmethod hnf ((A csparse) &optional (i0 0))
  (with-csparse-slots (m n cols) A
    (let ((colz (make-array n :adjustable t :fill-pointer n)))
      (declare (vector colz))
      (map-into colz #'copy-list cols)
      (hnf colz i0)
      (reset-markowitz
       (make-csparse :m m :n (length colz)
		     :cols (copy-seq colz) ;; gc-help CONSIDER HERE
		     :rlen (make-array m :initial-element -1)
		     :clen (make-array (length colz) :initial-element -1))))))

(defmethod hnf ((A vector) &optional (i0 0))
  (declare (vector A) (fixnum i0))
  (do ((j0 (length A) (1- j0))
       (j1 (1- (length A)) (1- j1)) ;; j1 = j0 - 1 always
       (i-piv -1)
       (e-piv nil)
       (j-piv -1)
       (e-other nil)
       (j-other -1))
      ((< j1 0))
    (declare (fixnum j0 j1 i-piv j-piv j-other))
    ;; The active region is i0 <= i < infinity, 0 <= j < j0.
    ;; We do column operations until there is a unique non-zero
    ;; column in the active region whose last index is maximal.  We
    ;; put that column into position j1 := j0 - 1 and use its last
    ;; entry to clear out the rest of its row.
    (block seek-unique-pivot-col
      (loop
	(setq i-piv -1 e-piv nil e-other nil)
	(dotimes-f (j j0)
	  (when (aref A j)
	    (let* ((e (first (last (aref A j))))
		   (i-lo (sp-i e)))
	      (declare (fixnum i-lo))
	      (when (>= i-lo i0)
		(cond ((or (null e-piv) (> i-lo i-piv))
		       (setq e-piv e i-piv i-lo j-piv j))
		      ((= i-lo i-piv)
		       (setq e-other e j-other j)
		       (return))))))) ;; exit the dotimes on j
	(cond ((null e-piv)
	       ;; The ending.  First, move non-zero col's to the left.
	       (do ((k 0 (1+ k))
		    (l 0)
		    (n (length A)))
		   ((= k n))
		 (declare (fixnum k l n))
		 (unless (aref A k)
		   (maxf l (1+ k)) ;; handling of l could be more elegant
		   (till (or (= l n) (aref A l))
		     (incf l))
		   (if (= l n)
		       (return)
		     (setf (aref A k) (aref A l)
			   (aref A l) '()))))
	       ;; Second, pop the zero col's off.
	       (till (or (zerop (length A)) (aref A (1- (length A))))
		 (vector-pop A))
	       (return-from hnf A)) ;; End of ending.
	      ((null e-other)
	       (return-from seek-unique-pivot-col))
	      (t
	       ;; Here two columns are competing for lowest entry.
	       (when (> (sp-euc-norm e-piv)
			(sp-euc-norm e-other))
		 (psetf (aref A j-piv) (aref A j-other)
			(aref A j-other) (aref A j-piv))
		 (psetf e-piv e-other
			e-other e-piv))
	       (v-alter-f (aref A j-other)
			  (sp-neg-closest-quotient e-other e-piv)
			  (aref A j-piv))))))
    ;; Here col j-piv is the unique col with lowest entry.  That
    ;; entry is e-piv in row i-piv.
    (unless (= j-piv j1)
      (psetf (aref A j-piv) (aref A j1)
	     (aref A j1) (aref A j-piv))
      (setq j-piv j1))
    ;; Next "minusp" clause is specific to Z.  See paragraph near the end.
    (when (and (sp-z-p e-piv) (minusp (sp-integer-value e-piv)))
      (v-negate-f (aref A j-piv))
      (setq e-piv (sp-negate e-piv)))
    (do ((j 0 (1+ j)))
	((= j (length A)))
      (declare (fixnum j))
      (unless (= j j-piv)
	(let ((e (v-get (aref A j) i-piv)))
	  (when e
	    (let ((q (sp-neg-closest-quotient e e-piv)))
	      (unless (sp-zerop q)
		(v-alter-f (aref A j) q (aref A j-piv))
		(setq e (sp-add e (sp-mult q e-piv)))) ;; = e after alter
	      ;; If q gives the best result for e, but the result has
	      ;; a negative value, does it follow that q+1 gives the
	      ;; best result with a positive value?  Over Z, the
	      ;; answer is yes.  Over fields, the question never comes
	      ;; up, because all "e after alter"'s have zero value.
	      (unless (sp-zerop e)
		(assert (sp-z-p e) ()
		  "hnf is only implemented over Z and over fields.")
		(when (minusp (sp-integer-value e))
		  (v-add-f (aref A j) (aref A j-piv)))))))))))

;;; ==================== Restricted to D = F_p ====================

(defstruct (perm-ech (:predicate is-perm-ech))
  "Say A is an m by n csparse of rank r defined over the field F_p.  A
perm-ech object realizes a matrix decomposition A = P E Q where P is an
m by m perm, E is an m by n matrix of rank r in column-echelon form, and
Q is n by n and invertible.  The main ideas are that E is too big to
store in RAM and that Q is not stored at all.  The decomposition is
stored in two files on disk, echp[fc].txt and eche[fc].txt, where fc
['file counter'] is a non-negative integer.  echp has three objects, P
n piv-i-list, basically the same bookkeeping information that a
perm-ech object holds in RAM.  eche has r sparse-v's, one per line.
We assume sparse-elts are stored in the usual way as (index . value)
with value in [0,p).  piv-i-list is the sorted list of the indices i
of rows of E which have a pivot."
  P n piv-i-list fc)

(defmethod m-num-rows ((pe perm-ech))
  (m-num-rows (perm-ech-P pe)))

(defmethod m-num-cols ((pe perm-ech))
  (perm-ech-n pe))

(defmethod rank ((pe perm-ech))
  (length (perm-ech-piv-i-list pe)))

(defmethod num-units ((pe perm-ech))
  (rank pe))

(defmethod torsion ((pe perm-ech))
  '())

(defmethod m-zerop ((pe perm-ech))
  (endp (perm-ech-piv-i-list pe)))

(defgeneric make-perm-ech-from-csparse (A)
  (:documentation
"Grab a new fc, block-triangularize A, dump the cols to eche[fc].txt
while removing them from RAM, ask the user to call ge.exe to
overwrite eche[fc].txt with the column-echelon form, stop and wait for
ge.exe to finish, and finally write out echp[fc].txt.  Return a
perm-ech object."))

;; The next method is correct under ACL, but is commented out
;; for general release because it uses ACL's regular expressions.
#|
(defmethod make-perm-ech-from-csparse ((A csparse))
  ;; TO DO: we ought to write n to echp[fc].txt before the call to
  ;; ge.exe.  The latter is prone to crash, and there's no sense in
  ;; losing the value of n.  We could write nil n nil.
  (with-csparse-slots (m n) A
    (multiple-value-bind (size-list P Q) (block-triangularize-3 A)
      (declare (ignore size-list Q))
      (let* ((fc (new-file-counter))
	     (echp-name (format nil "echp~D.txt" fc))
	     (eche-name (format nil "eche~D.txt" fc))
	     (sample-elt nil))
	(with-csparse-slots (cols) A
	  (with-open-file (so-e eche-name :direction :output :if-exists :supersede)
	    (dotimes-f (j n)
	      (when (svref cols j)
		(unless sample-elt
		  (setq sample-elt (first (svref cols j)))
		  (assert (sp-f_p-p sample-elt) ()
		    "Currently perm-ech is only implemented for F_p."))
		(format-flat so-e "~S~%" (svref cols j))
		(setf (svref cols j) '())))))
	(when sample-elt ;; else A = 0
	  (break "A ~D by ~D matrix has been removed from RAM and~&written to disk as ~A.  The entries are in~&the field ~A.  Please store the column-echelon form~&under the same filename, then continue from this break." m n eche-name (sp-ring-name sample-elt)))
	(let ((re-sv-head (excl:compile-re "^[(][(]([0-9]+) [.] 1[)]" :return :string #|:back-end regexp:native|#)) ;; not ANSI CL
	      (piv-i-list '()))
	  (with-open-file (so-p echp-name :direction :output :if-exists :supersede)
	    (format-flat so-p "~S~%~D~%(" P n)
	    (with-open-file (si-e eche-name)
	      (do ((line (read-line si-e nil) (read-line si-e nil)))
		  ((null line))
		(multiple-value-bind (matched-p match i) (excl:match-re re-sv-head line) ;; not ANSI CL
		  (declare (ignore match) (string i))
		  (assert matched-p ()
		    "Regexp '((index . 1)' for head of an sv didn't match ~A" line)
		  (format-flat so-p "~A " i)
		  (push (parse-integer i) piv-i-list))))
	    (format-flat so-p ")~%"))
	  (make-perm-ech :P P :n n :piv-i-list (nreverse piv-i-list) :fc fc))))))
|#

(defun make-perm-ech-from-disk (fc)
  "Reads echp[fc].txt and returns a perm-ech object for it."
  (assert (typep fc 'nnfixnum))
  (with-open-file (si (format nil "echp~D.txt" fc))
    (let ((P (read))
	  (n (read))
	  (piv-i-list (read)))
      (assert (and (perm-p P) (typep n 'nnfixnum) (listp piv-i-list)
		   (<= (length piv-i-list) n) (every #'integerp piv-i-list)))
      (let ((m (m-num-rows P)))
	(assert (typep m 'nnfixnum))
	(when piv-i-list
	  (assert (<= 0 (the integer (first piv-i-list))))
	  (do ((tail piv-i-list (rest tail)))
	      ((endp (rest tail))
	       (assert (< (first tail) (the nnfixnum m))))
	    (assert (< (the integer (first tail)) (the integer (second tail)))))))
      (make-perm-ech :P P :n n :piv-i-list piv-i-list :fc fc))))

(defmacro do-perm-ech-cols ((col pe &optional result) &body body)
  "Read pe's eche[fc].txt to get a sequence of sparse-v's, and
execute the body with col bound to each sparse-v in order."
  (let ((si (gensym)))
    `(with-open-file (,si (format nil "eche~D.txt" (perm-ech-fc ,pe)))
       (do ((,col (read ,si nil) (read ,si nil)))
	   ((null ,col) ,result)
	 (declare (type sparse-v ,col))
	 ,@body))))

;;; ------------------------- Wiedemann methods -------------------------

(defun berlekamp-massey (s nn p &key bb cc tt)
  "The Berlekamp-Massey algorithm over the field K = F_p.  Here nn >= 0
and p > 0 is a prime.  s is an array of >= 2*nn terms from K.  [Any
field K can be used after appropriate changes.]
  Elements of K[x] are represented as arrays, with the i-th entry
being the coefficient of x^i.  
  bb, cc and tt are in K[x].  In ordinary use, don't provide them.
But if the function is going to be called many times for the same nn,
you can pass in fixed scratch arrays.
  Return two values: the degree of the unique monic annihilator
polynomial of minimal degree in K[x], and cc overwritten with the
coefficients of that polynomial.
  Source: Maple code from daveagp on PlanetMath.org, 7 Nov 2007.  The
Maple code says it's a transliteration of Massey, _Shift-register
synthesis and BCH decoding_, IEEE Trans. Inform. Theory,
15(1):122-127, 1969."
  (declare (fixnum nn) (integer p))
  (assert (>= (length s) (* 2 nn)) ()
    "s has length ~D, but should have length >= 2*~D." (length s) nn)
  (let ((b 1) (d 1) ;; in K
	(ll 0) (k 1) ;; counters
	(deg-cc -1) ;; degree of the polynomial cc
	(degbd (+ (* 2 nn) 1))) ;; array length to hold up to degree 2*nn
    (declare (integer b d) (fixnum ll k deg-cc degbd))
    (macrolet ((mod-p (x)
		 `(the integer (mod (the integer ,x) p)))
	       (create-if-needed (x)
		 `(unless ,x (setq ,x (make-array degbd)))))
      (labels ((update-cc ()
		 (let ((d-over-b (mod-p (* d (inv-mod b p)))))
		   (declare (integer d-over-b))
		   (do ((i 0 (1+ i))
			(i0 k (1+ i0))) ;; alias for i+k
		       ((>= i degbd))
		     (declare (fixnum i i0))
		     (unless (zerop (svref bb i))
		       (setf (svref cc i0)
			 (mod-p (- (svref cc i0)
				   (* d-over-b (svref bb i)))))
		       (if (and (> i0 deg-cc) (/= (svref cc i0) 0))
			   (setq deg-cc i0)
			 (when (= i0 deg-cc)
			   (till (or (< deg-cc 0) (/= (svref cc deg-cc) 0))
			     (decf deg-cc)))))))))
	(create-if-needed bb)
	(setf (svref bb 0) 1)
	(fill bb 0 :start 1)
	(create-if-needed cc)
	(setf (svref cc 0) 1)
	(fill cc 0 :start 1)
	(setq deg-cc 0)
	(create-if-needed tt)
	(dotimes-f (n (* 2 nn) (values deg-cc cc))
	  (setq d (mod-p (svref s n)))
	  (do ((i 1 (1+ i))
	       (j (1- n) (1- j)))
	      ((> i ll))
	    (declare (fixnum i j))
	    (setq d (mod-p (+ d (* (svref cc i) (svref s j))))))
	  (when (= d 0)
	    (incf k))
	  (when (and (/= d 0) (> (* 2 ll) n))
	    (update-cc)
	    (incf k))
	  (when (and (/= d 0) (<= (* 2 ll) n))
	    (map-into tt #'identity cc)
	    (update-cc)
	    (map-into bb #'identity tt)
	    (setq ll (- (1+ n) ll)
		  k 1
		  b d)))))))

(defun wiedemann-square-dependency (A nn)
  "Tries to find a non-zero vector x such that A * x = 0.  The point
of Wiedemann's methods is to work without any fill-in at all.
  Wiedemann's algorithm requires the underlying domain to be a
finite field.  The implementation here requires F_p for fixnum p.
More precisely, p must be prime, positive, and small enough that
p^2 + p < 2^29.
  If repeated calls to this function can't find such an x, the matrix
probably has full rank.
  Arguments: A is an m by n with m and n >= nn.  Columns j >= nn are
ignored, but it is an error if the i,j-th position has a non-zero
entry for some i >= nn and j < nn.
  Returns two values:
[.] x if it can find it, nil if it can't;
[.] p [or 1 in the degenerate case when A is zero].
  We follow Wiedemann, _Solving sparse linear equations over finite
fields_, IEEE Transactions on Information Theory, vol. IT-32, no. 1,
Jan. 1986, pp. 54-62.  This function follows the first two paragraphs
of Section II."
  (declare (type csparse A) (fixnum nn))
  (let ((sample-elt (first (some #'identity (csparse-cols A)))))
    (unless sample-elt ;; A is zero
      (return-from wiedemann-square-dependency
	(values (make-array nn :initial-element 1) 1)))
    (assert (sp-f_p-p sample-elt) ()
      "The matrix must be defined mod p, not over ~A."
      (sp-ring-name sample-elt))
    (let ((p (sp-f_p-p sample-elt))
	  (b (make-array nn))
	  (u (make-array nn))
	  ;; s, bb, f (a.k.a. cc), and tt are for berlekamp-massey.
	  (s (make-array (* 2 nn)))
	  (bb (make-array (1+ (* 2 nn))))
	  (f (make-array (1+ (* 2 nn))))
	  (tt (make-array (1+ (* 2 nn))))
	  (deg-f -1)
	  ;; For a-mult
	  (a-mult-in (make-array nn))
	  (a-mult-out (make-array nn)))
      (declare (type nnfixnum p) (fixnum deg-f)
	       (simple-vector b u s bb f tt a-mult-in a-mult-out))
      ;; Initialize b and u at random.
      (dotimes-f (j nn)
	(setf (svref b j) (random p)
	      (svref u j) (random p)))
      (macrolet ((Z (x) `(the nnfixnum ,x))
		 (mod-p (x) `(Z (rem (Z ,x) p)))) ;; MUST HAVE x, p >= 0
	(labels ((a-mult ()
		   "Copy a-mult-out into a-mult-in, then overwrite a-mult-out with A * a-mult-in."
		   (dotimes-f (j nn)
		     (setf (svref a-mult-in j) (svref a-mult-out j)))
		   (fill a-mult-out 0)
		   (with-csparse-slots (cols) A
		     (dotimes-f (j nn)
		       (let ((a-mult-in-j (svref a-mult-in j)))
			 (declare (type nnfixnum a-mult-in-j))
			 (unless (zerop a-mult-in-j)
			   (dolist (e (svref cols j))
			     (let ((i (sp-i e)))
			       (declare (type nnfixnum i))
			       (setf (svref a-mult-out i)
				 (mod-p (+ (Z (svref a-mult-out i))
					   (Z (* (Z (sp-integer-lift e))
						 a-mult-in-j)))))))))))))
	  (dotimes-f (ell (* 2 nn))
	    ;; Put A^ell * b into a-mult-out.
	    (if (= ell 0)
		(map-into a-mult-out #'identity b)
	      (a-mult))
	    ;; Put (u dot (A^ell * b)) into s[ell].
	    (setf (svref s ell) 0)
	    (dotimes-f (i nn)
	      (setf (svref s ell)
		(mod-p (+ (Z (svref s ell))
			  (Z (* (Z (svref u i))
				(Z (svref a-mult-out i)))))))))
	  (setq deg-f
	    (berlekamp-massey s nn p :bb bb :cc f :tt tt))
	  ;; For some reason, the coefficients are in the wrong
	  ;; order, and we have to flip them.
	  (do ((jj0 0 (1+ jj0))
	       (jj1 deg-f (1- jj1)))
	      ((>= jj0 jj1))
	    (declare (fixnum jj0 jj1))
	    (psetf (svref f jj0) (svref f jj1)
		   (svref f jj1) (svref f jj0)))
	  (let ((x u)) ;; reuse u's space for x
	    (declare (simple-vector x))
	    (fill x 0)
	    (let ((ell0 0)) ;; deg of trailing non-zero term
	      (till (or (> ell0 deg-f) (not (zerop (Z (svref f ell0)))))
		    (incf ell0))
	      (do ((ell ell0 (1+ ell)))
		  ((> ell deg-f))
		(declare (fixnum ell))
		;; Put A^(ell-ell0) * b into a-mult-out.
		(if (= ell ell0)
		    (map-into a-mult-out #'identity b)
		  (a-mult))
		;; Increment x with f[ell] * a-mult-out.
		(dotimes-f (i nn)
		  (setf (svref x i)
		    (mod-p (+ (Z (svref x i))
			      (Z (* (Z (svref f ell))
				    (Z (svref a-mult-out i)))))))))
	      (when (every #'zerop x)
		(cerror "Keep going.  It may not be a problem."
			"Warning: ambiguous case.~&f's non-zero coeffs have ~D <= deg <= ~D.  nn = ~D." ell0 deg-f nn)
		(return-from wiedemann-square-dependency
		  (values nil p))))
	    ;; Exit with success, soon.  All we have to do is compute
	    ;; A * x, A^2 * x, A^3 * x, etc.  One of these must be
	    ;; zero, and the previous one will be the desired
	    ;; dependency.
	    (map-into a-mult-out #'identity x)
	    (till (every #'zerop a-mult-out)
	      (a-mult))
	    (return-from wiedemann-square-dependency
	      (values a-mult-in p))))))))

(defun wiedemann-square-verify (A nn)
  "Run wiedemann-square-dependency on the input, then check directly
that the result x satisfies A x = 0 as it's supposed to.  Do nothing
if x is null.  Give an assert failure if A x /= 0.  Columns j >= nn
are ignored.  Returns whatever wiedemann-square-dependency returns."
  (multiple-value-bind (x p) (wiedemann-square-dependency A nn)
    (declare (integer p))
    (when x
      (macrolet ((Z (y) `(the integer ,y))
		 (mod-p (y) `(Z (mod (Z ,y) p))))
	(let ((prod (make-array nn :initial-element 0)))
	  (with-csparse-slots (cols) A
	    (dotimes-f (j nn)
	      (dolist (e (svref cols j))
		(setf (svref prod (sp-i e))
		  (mod-p (+ (Z (svref prod (sp-i e)))
			    (Z (* (Z (sp-integer-lift e))
				  (Z (svref x j))))))))))
	    (assert (every #'zerop prod) ()
	      "A * x /= 0 for A =~&~A~&x =~A" A x))))
    (values x p)))

(defun wiedemann-square-test (n r make-sp)
  "Run a random test of wiedemann-square.  Generate a random n by n
matrix of rank <= r [almost certainly = r].  Pass it to
wiedemann-square-verify, which runs the test.  make-sp is a sparse-elt
constructor for some field of prime order.  Returns whatever
wiedemann-square-verify returns."
  (let ((p (sp-f_p-p (funcall make-sp 0 1)))
	(input-list-A '()))
    (assert p ()
      "The sparse-elt constructor make-sp is not working mod p.")
    (dotimes (k (* n r))
      (push (random p) input-list-A))
    (let ((A (input-csparse n n input-list-A make-sp)))
      (when (< r n)
	(dotimes (k n)
	  (alter-row A (random n) (funcall make-sp -1 (random p)) (random n))
	  (alter-col A (random n) (funcall make-sp -1 (random p)) (random n))))
      (wiedemann-square-verify A n))))

(defun wiedemann-winnow (A &optional (corner 0))
  "Given an m by n csparse A, with m <= n, over a ring that is supported
by wiedemann-square-dependency.  We destructively remove columns from A
until there are at most m columns, while guaranteeing that the image is
unchanged.  If corner > 0, we call wiedemann-winnow-aux instead [q.v.]
  As of this writing, I'm not sure what happens if the first m columns
attain full rank.
  Ways to improve this code... Remove the restriction m <= n.  Allow
full rank m by coding up more Wiedemann methods [for in fact, the
full-rank case of Wiedemann is the conventional case in his original
paper].  Remove both rows and columns until the active portion has
full rank.  Keep track of the change of basis on the row side, so that
we still know the image."
  (with-csparse-slots (m n cols) A
    (assert (<= m n) ()
      "This version of the winnower requires m <= n.")
    (assert (<= 0 corner m) ()
      "Violated 0 <= corner (~D) <= m (~D)." corner m)
    (when (> corner 0)
      (return-from wiedemann-winnow
	(wiedemann-winnow-aux A corner)))
    (when *verbose*
      (format t "~&Starting wiedemann-winnow on a ~D by ~D matrix, ~A~&" m n (time-stamp)))
    (let ((rh-cols (make-array (- n m) :fill-pointer 0))
	  (max-tries 10))
      (declare (vector rh-cols) (type nnfixnum max-tries))
      (macrolet ((rh-len () '(the nnfixnum (fill-pointer rh-cols))))
	;; Move columns to the right of the square out into a pool.
	(do ((j m (1+ j)))
	    ((= j n))
	  (declare (type nnfixnum j))
	  (awhen (svref cols j)
	    (vector-push it rh-cols)
	    (setf (svref cols j) '())))
	;; If the square happens to have some zero columns, fill them
	;; from the pool.
	(dotimes-f (j m)
	  (unless (svref cols j)
	    (if (> (rh-len) 0)
		(setf (svref cols j) (vector-pop rh-cols))
	      (return))))
	;; Main loop.
	(loop while (> (rh-len) 0) do
	  (when (and *verbose* (zerop (mod (rh-len) 10)))
	    (format t "~&    ~D to go ~A~&" (rh-len) (time-stamp)))
	  (dotimes-f (tries max-tries
			    ;; We hope tries will never get beyond 0.
			    (assert nil ()
			      "Main loop failed after ~D tries." max-tries))
	    (let ((x (wiedemann-square-dependency A m)))
	      (when x
		(let ((j (position-if-not #'zerop x)))
		  ;; Column j is dependent on others in the square.  Set
		  ;; it to zero, then put one from the pool into its place.
		  (setf (svref cols j) (vector-pop rh-cols))
		  ;; Return from the loop on 'tries'.
		  (return)))))))))
  (reset-markowitz A))

(defun wiedemann-winnow-aux (A corner)
  "Move [corner,m) by [corner,n) of A to a new csparse A0, apply
wiedemann-winnow to A0, and move back."
  (declare (type nnfixnum corner))
  (when *verbose*
    (format t "~&Starting wiedemann-winnow-aux ~A~&" (time-stamp)))
  (with-csparse-slots (m n cols) A
    (let ((m0 (- m corner))
	  (n0 (- n corner)))
      (declare (type nnfixnum m0 n0))
      (let ((A0 (make-csparse-zero m0 n0)))
	(with-csparse-slots ((cols0 cols)) A0
	  (do ((j corner (1+ j))
	       (j0 0 (1+ j0)))
	      ((= j0 n0))
	    (declare (type nnfixnum j j0))
	    (let ((v (svref cols j)))
	      (setf (svref cols j) '())
	      (do ((w v (rest w)))
		  ((endp w))
		(let ((e (first w)))
		  (setf (first w)
		    (copy-sp e (- (sp-i e) corner)))))
	      (setf (svref cols0 j0) v)))
	  (wiedemann-winnow A0 0)
	  (do ((j corner (1+ j))
	       (j0 0 (1+ j0)))
	      ((= j0 n0) (reset-markowitz A))
	    (declare (type nnfixnum j j0))
	    (let ((v (svref cols0 j0)))
	      (setf (svref cols0 j0) '())
	      (do ((w v (rest w)))
		  ((endp w))
		(let ((e (first w)))
		  (setf (first w)
		    (copy-sp e (+ (sp-i e) corner)))))
	      (setf (svref cols j) v))))))))

;;; ==================== Restricted to D = Z ====================

(defun csparse-integer-length (a)
  "Input: a csparse, which must be defined over D = Z.  Returns
two values, the average and maximum integer-length taken over all
non-zero values in the csparse."
  (let ((sum 0)
	(mx 0)
	(tally 0))
    (declare (integer sum mx tally))
    (with-csparse-slots (cols) a
      (map nil #'(lambda (col)
		   (declare (type sparse-v col))
		   (map nil #'(lambda (e)
				(let ((len (integer-length
					    (sp-integer-value e))))
				  (declare (integer len))
				  (incf sum len)
				  (maxf mx len)
				  (incf tally)))
			col))
	   cols))
    (values (if (zerop tally) 0 (/ sum tally)) mx)))

(defun v-norm-sq (v)
  "Returns the square of the norm of a sparse-v, as a double-float.
Requires D = Z."
  (declare (type sparse-v v))
  (catch 'overflow
    (handler-bind ((simple-error
		    #'(lambda (condition)
			(declare (ignore condition))
			(throw 'overflow most-positive-double-float))))
      (let ((ans 0.0d0))
	(declare (double-float ans))
	(dolist (e v ans)
	  (let ((val (coerce (sp-integer-value e) 'double-float)))
	    (incf ans (* val val))))))))

(defun sort-by-norm-sq (cols corner)
  "Sort cols, an array of sparse-v's, by increasing v-norm-sq."
  (declare (simple-vector cols) (type nnfixnum corner))
  (let ((arr (subseq cols corner)))
    (map-into arr #'(lambda (l) (cons (v-norm-sq l) l)) arr)
    (sortf arr #'(lambda (l1 l2)
		   (< (the double-float (first l1))
		      (the double-float (first l2)))))
    (dotimes-f (j (- (length cols) corner))
      (setf (svref cols (+ j corner)) (rest (svref arr j))))))

(defun hit-with-lll (A corner)
  "Perform Lenstra-Lenstra-Lovasz on successive vertical strips
of width up to *lll-width* in the csparse A, overwriting A with
the results.  Returns the altered A.  Requires D = Z."
  (declare (type nnfixnum corner))
  (with-csparse-slots (m n cols) A
    (sort-by-norm-sq cols corner)
    (let ((start corner)
          (show-lll (and *verbose* (not *show-csw*))))
      (declare (type nnfixnum start))
      (till (or (>= start n) (not (endp (svref cols start))))
        (incf start)) ;; move past empty columns at left
      (when show-lll
        (format t "~&    Running LLL from columns ~D to ~D ~A~&" start n (time-stamp)))
      (do ((j start (+ j *lll-width*)))
          ((>= j n))
        (declare (type nnfixnum j))
        (let ((j1 (min (+ j *lll-width*) n)))
          (declare (type nnfixnum j1))
          (let ((dd (csparse-move-to-dense A corner m j j1)))
            (declare (type dense-matrix-z dd))
            (when show-lll
              (format t "~&       ~D to ~D ~A~&" j j1 (time-stamp)))
            (when *show-csw*
              (csw-set-yellow j j1))
            (do-lll dd)
            (csparse-move-from-dense A dd corner m j j1))))
      (when *show-csw*
        (csw-set-yellow n n))
      (reset-markowitz A))))

(defun csparse-move-from-dense (ca da i0 i1 j0 j1)
  "Destructively replaces a rectangular block of the csparse ca with
the contents of the dense-matrix-z da.  The resulting block is
thus defined over D = Z.  The block is
i0 <= i < i1, j0 <= j < j1.  We require da to have size i1-i0 by j1-j0.
Returns the altered ca.  Does not set rlen and clen; if you ever
call this function directly, call (reset-markowitz ca) at the end."
  (declare (type dense-matrix-z da) (type nnfixnum i0 i1 j0 j1))
  (with-csparse-slots (m n cols) ca
    (assert (and (<= 0 i0) (<= i1 m) (= (- i1 i0) (array-dimension da 0)))
        (ca da i0 i1) "Rows out of bounds.")
    (assert (and (<= 0 j0) (<= j1 n) (= (- j1 j0) (array-dimension da 1)))
        (ca da j0 j1) "Columns out of bounds.")
    (do ((j j0 (1+ j))
         (dj 0 (1+ dj)))
        ((>= j j1) ca)
      (declare (type nnfixnum j dj))
      (let ((new-mid '())
            (new-mid-last nil))
        (declare (type sparse-v new-mid new-mid-last))
        (do ((i (1- i1) (1- i))
             (di (- i1 i0 1) (1- di)))
            ((< i i0))
          (declare (type fixnum i di))
          (unless (zerop (aref da di dj))
            (push (make-sp-z i (aref da di dj)) new-mid)
            (unless new-mid-last
              (setq new-mid-last new-mid))))
        (with-splicer (svref cols j)
          (till (or (splicer-endp) (>= (sp-i (splicer-read)) i0))
            (splicer-fwd))
          (multiple-value-bind (left left-last mid-right) (splicer-split)
            (declare (type sparse-v left left-last mid-right))
            (unless (endp new-mid)
              (if (endp left)
                  (setf (svref cols j) new-mid)
                (rplacd left-last new-mid))
              (setq left-last new-mid-last))
            (till (or (endp mid-right) (>= (sp-i (first mid-right)) i1))
              (pop mid-right))
            (if (endp (svref cols j))
                (setf (svref cols j) mid-right)
              (rplacd left-last mid-right))))))))

(defun csparse-move-to-dense (ca i0 i1 j0 j1)
  "Destructively removes a rectangular block of the csparse ca,
putting the entries into a dense-matrix-z and returning the latter.
If the block isn't defined over Z, sp-integer-value will signal an
error.  The block is i0 <= i < i1, j0 <= j < j1.  Does not set rlen
and clen; if you ever call this function directly,
call (reset-markowitz ca) at the end."
  (declare (type nnfixnum i0 i1 j0 j1))
  (with-csparse-slots (m n cols) ca
    (assert (and (<= 0 i0 i1) (<= i1 m)) (ca i0 i1) "Rows out of bounds.")
    (assert (and (<= 0 j0 j1) (<= j1 n)) (ca j0 j1) "Columns out of bounds.")
    (let ((da (make-dense-matrix-z (- i1 i0) (- j1 j0))))
      (declare (type dense-matrix-z da))
      (do ((j j0 (1+ j))
           (dj 0 (1+ dj)))
          ((>= j j1) da)
	(declare (type nnfixnum j dj))
        (with-splicer (svref cols j)
          (loop
            (if (splicer-endp)
                (return)
              (let ((i (sp-i (splicer-read))))
                (declare (type nnfixnum i))
                (if (>= i i1)
                    (return)
                  (if (< i i0)
                      (splicer-fwd)
                    (let ((di (- i i0)))
                      (setf (aref da di dj) (sp-integer-value (splicer-read)))
                      (splicer-delete))))))))))))

(defun csparse-move-to-pari (A j0 j1)
  "Destructively removes the strip j0 <= j < j1 from the
csparse A, and writes it out to a file in Pari's matrix format.
For this we require D = Z.
Let i0 be the least row index that occurs in these columns; the empty
rows 0 <= i < i0 of the strip are not written out.  Let n0 be the
number of non-zero columns in the strip; columns that are all
zero are not written out.  Thus the size of the matrix written out
is (m - i0) by n0.
  Returns three values: i0, n0, fc.  Here fc is a non-negative
integer, unique in each call to the function.  The file written
out is named pari??.txt, where ?? is fc.  Does not set rlen and clen;
if you ever call this function directly, call (reset-markowitz A)
at the end."
  (declare (type nnfixnum j0 j1))
  (with-csparse-slots (m n cols) A
    (assert (<= 0 j0 j1 n) ()
      "Violated col ranges 0 <= ~D <= ~D <= ~D." j0 j1 n)
    (let ((i0 m)
	  (blank-j (make-hash-table :size (- j1 j0))))
      (declare (type nnfixnum i0))
      (do ((j j0 (1+ j)))
	  ((= j j1))
	(declare (type nnfixnum j))
	(if (svref cols j)
	    (minf i0 (sp-i (first (svref cols j))))
	  (puthash j t blank-j)))
      (labels ((is-blank (j) (nth-value 1 (gethash j blank-j))))
	(let ((n0 (- j1 j0 (hash-table-count blank-j)))
	      (j1-last (1- j1))
	      (m-min1 (1- m))
	      (fc (new-file-counter)))
	  (declare (type nnfixnum n0) (fixnum j1-last m-min1))
	  (till (or (< j1-last j0) (not (is-blank j1-last)))
	    (decf j1-last))
	  (with-open-file (s (format nil "pari~D.txt" fc)
			   :direction :output
			   :if-exists :supersede
			   :if-does-not-exist :create)
	    (format s "[")
	    (do ((i i0 (1+ i)))
		((= i m))
	      (do ((j j0 (1+ j)))
		  ((> j j1-last))
		(unless (is-blank j)
		  (let ((val 0))
		    (declare (integer val))
		    (when (svref cols j)
		      (let* ((e (first (svref cols j)))
			     (e-i (sp-i e)))
			(declare (type nnfixnum e-i))
			(if (< e-i i)
			    (error "Entry at ~D,~D but expected row ~D."
				   e-i j i)
			  (when (= e-i i)
			    (setq val (sp-integer-value e))
			    (pop (svref cols j))))))
		    (format s "~D" val))
		  (if (< j j1-last)
		      (format s ", ")
		    (if (< i m-min1)
			(format s "; ")
		      (format s "]")))))))
	  (values i0 n0 fc))))))

(defun csparse-move-from-pari (A j0 i0 n0 fc)
  "The file pariH??.txt, where ?? is fc, contains a matrix of
integers in Pari format with n0 or fewer columns.  We overwrite the
csparse A with the Pari matrix.  The i,j entry of the Pari matrix
goes to the i0+i,j0+j entry of A.  Columns [j0,j0+n0) of A are
deleted beforehand.  At the end, the file is deleted.  Does not set
rlen and clen; if you ever call this function directly,
call (reset-markowitz ca) at the end."
  (declare (type nnfixnum j0 i0 n0))
  (let ((j1 (+ j0 n0))
	(filename (format nil "pariH~D.txt" fc)))
    (declare (type nnfixnum j1))
    (with-csparse-slots (m n cols) A
      (assert (<= 0 j0 j1 n) ()
	"Violated col ranges 0 <= ~D <= ~D <= ~D." j0 j1 n)
      (do ((jj j0 (1+ jj)))
	  ((= jj j1))
	(declare (type nnfixnum jj))
	(setf (svref cols jj) '()))
      (let ((i i0)
	    (j j0)
	    (sb (make-array 1000 :element-type 'character
			    :adjustable t :fill-pointer 0)))
	(declare (type nnfixnum i j) (type (vector character) sb))
	(with-open-file (s filename)
	  (loop
	    (let ((c (read-char s nil)))
	      (if (null c)
		  (return)
		(if (or (digit-char-p c) (char= c #\-))
		    (vector-push-extend c sb)
		  (unless (zerop (length sb))
		    (let ((val (parse-integer sb)))
		      (declare (integer val))
		      (assert (< i m) () "Ran off the bottom.")
		      (assert (< j j1) () "Ran off the right.")
		      (unless (zerop val)
			(push (make-sp-z i val) (svref cols j)))
		      (setf (fill-pointer sb) 0)
		      (incf j)
		      (when (or (char= c #\;) (char= c #\]))
			(setq j j0)
			(incf i)))))))))
	(unless (= m i)
	  (cerror "That's okay--keep going."
		  "The csparse has m = ~D, but the new part uses m = ~D."
		  m i))
	(delete-file filename))
      (do ((jj j0 (1+ jj)))
	  ((= jj j1))
	(declare (type nnfixnum jj))
	(setf (svref cols jj) (nreverse (svref cols jj)))))))

(defun disk-hnf-2-col-step-z (v w)
  "Assumes things its caller checked: v and w are both non-empty
and have the same first index i.  This version is strictly over Z.
disk-hnf-2-col-step calls this version when it's appropriate, and uses
a non-Z algorithm otherwise."
  (labels ((safe-scalar-mult (c x)
	     (declare (integer c) (type sparse-v x))
	     (if (= c 1)
		 x
	       (if (zerop c)
		   '()
		 (if (= c -1)
		     (mapcar #'sp-negate x)
		   (mapcar #'(lambda (e)
			       (make-sp-z (sp-i e) (* c (sp-integer-value e))))
			   x)))))
	   (safe-lin-combn (c x d y)
	     (declare (integer c d) (type sparse-v x y))
	     (if (zerop d)
		 (safe-scalar-mult c x)
	       (if (zerop c)
		   (safe-scalar-mult d y)
		 (let ((ans '())
		       (c-1-p (= c 1))
		       (d-1-p (= d 1)))
		   (declare (type sparse-v ans))
		   (till (and (endp x) (endp y))
		     (let ((ix (if (endp x) nil (sp-i (first x))))
			   (iy (if (endp y) nil (sp-i (first y)))))
		       (let ((x-only (and ix
					  (or (null iy)
					      (< (the nnfixnum ix)
						 (the nnfixnum iy)))))
			     (y-only (and iy
					  (or (null ix)
					      (< (the nnfixnum iy)
						 (the nnfixnum ix))))))
			 (if x-only
			     (let ((vx (sp-integer-value (pop x))))
			       (declare (integer vx))
			       (push (make-sp-z ix (if c-1-p
						       vx
						     (the integer (* c vx))))
				     ans))
			   (if y-only
			       (let ((vy (sp-integer-value (pop y))))
				 (declare (integer vy))
				 (push (make-sp-z iy (if d-1-p
							 vy
						       (the integer (* d vy))))
				       ans))
			     (let ((vx (sp-integer-value (pop x)))
				   (vy (sp-integer-value (pop y))))
			       (declare (integer vx vy))
			       (let ((vans (+ (the integer
						(if c-1-p
						    vx
						  (the integer (* c vx))))
					      (the integer
						(if d-1-p
						    vy
						  (the integer (* d vy)))))))
				 (declare (integer vans))
				 (unless (zerop vans)
				   (push (make-sp-z ix vans) ans)))))))))
		   (nreverse ans))))))
    (let ((a (sp-integer-value (first v)))
	  (b (sp-integer-value (first w)))
	  (i (sp-i (first v))))
      (declare (integer a b) (type nnfixnum i))
      (multiple-value-bind (a0 b0 d0)
	  (if (zerop (mod b a))
	      (values (if (> a 0) 1 -1) 0 (abs a)) ;; Cohen's patch
	    (ext-gcd a b))
	(declare (integer a0 b0 d0))
	;; a0 * a + b0 * b = d0 >= 0.
	(let ((a1 (truncate a d0))
	      (b1 (the integer (- (truncate b d0)))))
	  (declare (integer a1 b1))
	  ;; The matrix (a0 b0 | b1 a1) is in SL(2,Z).
	  (let ((new-v (safe-lin-combn a0 v b0 w))
		(new-w (safe-lin-combn b1 v a1 w)))
	    (declare (type sparse-v new-v new-w))
	    (assert (and (not (endp new-v))
			 (= i (sp-i (first new-v)))
			 (= d0 (sp-integer-value (first new-v)))
			 (or (endp new-w)
			     (< i (sp-i (first new-w))))) ()
	      "Didn't create staggered i's.")
	    (values new-v new-w)))))))

;;; -------------------- More linear algebra over Z --------------------

(defun m-inverse-image (a b)
  "See documentation for inverse-image.  Here a is a csparse
with linearly independent columns, and b an snf with both P's and Q's.
Returns a new csparse with linearly independent columns that maps to
the inverse image."
  (declare (type csparse a) (type snf b))
  (let ((c (csparse-copy a)))
    (declare (type csparse c))
    (with-slots (d use-p use-q) b
      (declare (type csparse d))
      (assert use-p ()
	"The second argument was computed without remembering the~&changes of coords on the target side.")
      (assert use-q ()
	"The second argument was computed without remembering the~&changes of coords on the source side.")
      (do-snf-p (p b)
	(m-mult (m-inverse p) c))
      (let ((nu (num-units b))
	    (r (rank b))
	    (colz (make-array 0 :adjustable t :fill-pointer t)) ;; gc-help CONSIDER HERE
	    (j-mid 0)) ;; 0 is a dummy value
	(declare (type nnfixnum nu r j-mid) (vector colz))
	(hnf-f c nu)
	(with-csparse-slots (m n cols) c
	  (setq j-mid n)
	  (block j-loop
	    (dotimes-f (j n)
	      (let ((y (svref cols j)))
		(declare (type sparse-v y))
	        (dolist (ey (the sparse-v y))
		  (let ((i (sp-i ey)))
		    (declare (type nnfixnum i))
		    (when (>= i nu)
		      (when (= j-mid n)
			(setq j-mid j))
		      (when (>= i r)
			(return-from j-loop)))))
		(when (< j-mid n)
		  (vector-push-extend y colz)))))
	  (do ((tor '() (cons (csparse-get d k k) tor))
	       (k (1- r) (1- k)))
	      ((< k nu)
	       (m-inverse-image-aux tor colz r)) ;; a major step
	    (declare (list tor) (fixnum k)))
	  (let ((n0 (+ j-mid (length colz) (- m r))))
	    (assert (<= n0 n) ()
	      "Sum (+ j-mid (length colz) (- m r)) = (+ ~D ~D (- ~D ~D)) = ~D exceeds ~D.  colz is ~A" j-mid (length colz) m r n0 n colz)
	    (let ((ans (make-csparse-zero m n0))
		  (j 0))
	      (with-csparse-slots ((cols-ans cols)) ans
		(dotimes-f (j0 j-mid)
		  (setf (svref cols-ans j) (svref cols j0))
		  (incf j))
		(dotimes-f (j0 (length colz))
		  (setf (svref cols-ans j) (aref colz j0))
		  (incf j))
		(do ((j0 r (1+ j0)))
		    ((>= j0 m))
		  (declare (type nnfixnum j0))
		  (setf (svref cols-ans j) (list (make-sp-z j0 1)))
		  (incf j)))
	      (reset-markowitz ans)
	      (do-snf-q (q b)
		(m-mult (m-inverse q) ans))
	      ans)))))))

(defun m-inverse-image-aux (tor colz r)
  ;; Overwrites colz and returns it.
  (declare (list tor) (vector colz) (type nnfixnum r))
  (if (endp tor)
      colz
    (let ((e (first tor)))
      (if (sp-unitp e)
	  (m-inverse-image-aux (rest tor) colz r)
	(let ((nu (sp-i e)) ;; the nu during this recursive pass
	      (p (caar (factor (sp-integer-value e))))
	      (n (length colz)))
	  (declare (type nnfixnum nu n) (type (integer 2 *) p))
	  (let ((aa (make-dense-matrix-mod-p-zero (- r nu) n p))
		(sp-p (make-sp-z -1 p)))
	    (declare (type dense-matrix-mod-p aa))
	    (with-dense-matrix-mod-p-slots ((a mat)) aa
	      (dotimes-f (j n)
		(dolist (ee (aref colz j))
		  (when (>= (sp-i ee) nu)
		    (setf (aref a (+ (* n (- (sp-i ee) nu)) j))
		      (rem (sp-integer-value ee) p)))))
	      (let* ((kk (m-ker aa))
		     (kk-a (mat kk))
		     (kerdim (m-num-cols kk)))
		(declare (dense-matrix-mod-p kk) (vector kk-a) (type nnfixnum kerdim))
		(dotimes-f (k kerdim)
		  (let ((sum '()))
		    (declare (type sparse-v sum))
		    (dotimes-f (j n)
		      (unless (zerop (aref kk-a (+ (* kerdim j) k)))
			(v-alter sum (make-sp-z -1 (aref kk-a (+ (* kerdim j) k))) (aref colz j))))
		    (vector-push-extend sum colz)))
		;; (length colz) is now n+kerdim.  Next loop is for first n.
		(dotimes-f (j n)
		  (dolist (e1 (the sparse-v (aref colz j)))
		    (when (and (>= (sp-i e1) nu)
			       (not (sp-divides sp-p e1)))
		      (v-scalar-mult-f (aref colz j) sp-p)
		      (return)))) ;; goto next j
		(hnf colz nu)
		;; The point of this exercise is that every entry of colz
		;; in rows >= nu should now be divisible by p.  Do the
		;; division.
		(dotimes-f (j (+ n kerdim))
		  (do ((tail (aref colz j) (rest tail)))
		      ((endp tail))
		    (let ((ee (first tail)))
		      (when (>= (sp-i ee) nu)
			(assert (sp-divides sp-p ee) ()
			  "The triangular region we thought was divisible by p isn't.")
			(rplaca tail (sp-divided-by ee sp-p))))))
		(m-inverse-image-aux
		 (mapcar #'(lambda (ee)
			     (assert (sp-divides sp-p ee) ()
			       "The elementary divisors we thought were divisible by p weren't.")
			     (sp-divided-by ee sp-p))
			 tor)
		 colz
		 r)))))))))

;;; ######################  Unit tests over Z  ######################

(block unit-tests-over-z
  ;; If make-sp-z throws an error, it means Z is unavailable.
  (handler-bind ((error #'(lambda (condition)
			    (declare (ignore condition))
			    (return-from unit-tests-over-z))))
    (make-sp-z 0 1))

  ;; Test for make-snf-from-disk.
  (unless (or (probe-file "snfd1126.txt")
              (probe-file "snfp1126.txt")
              (probe-file "snfb1126.txt")
              (probe-file "snfq1126.txt")
              (probe-file "snfh1126.txt"))
    (with-open-file (sd "snfd1126.txt" :direction :output)
      (format sd "3 3 2 (6)~%"))
    (with-open-file (sp "snfp1126.txt" :direction :output)
      (format sp "~S" (make-perm2 0 2)))
    (with-open-file (sb "snfb1126.txt" :direction :output)
      (format sb "~S" (make-perm2 0 2)))
    (with-open-file (sq "snfq1126.txt" :direction :output)
      (format sq "~S" (make-perm2 1 2)))
    (with-open-file (sh "snfh1126.txt" :direction :output)
      (format sh "~S" (make-perm2 1 2)))
    (let ((snf-disk (make-snf-from-disk 1126))
	  (A (input-csparse 3 3 '(0 6 0 0 0 1 1 0 0))))
      (integrity-check snf-disk :orig A :message "make-snf-from-disk: "))
    (delete-file "snfd1126.txt")
    (delete-file "snfp1126.txt")
    (delete-file "snfb1126.txt")
    (delete-file "snfq1126.txt")
    (delete-file "snfh1126.txt"))

  ;; Tests for Hermite normal form.
  (let ((a (input-csparse 3 2 '(8 19 -3 7 6 5))))
    (integrity-check a)
    (hnf-f a 0)
    (assert (equalp a (input-csparse 3 2 '(74 63 57 47 0 1)))))
  (let ((a (input-csparse 3 2 '(8 19 -3 7 6 5)))) ;; same test for disk-hnf
    (hit-with-disk-hnf a)
    (hnf-f a 0)
    (assert (equalp a (input-csparse 3 2 '(74 63 57 47 0 1)))))
  (let ((a (input-csparse 3 3 '(1 3 9 1 4 16 1 7 49))))
    (integrity-check a)
    (hnf-f a 0)
    (assert (equalp a (input-csparse 3 3 '(4 0 1 0 3 1 0 0 1)))))
  (let ((a (input-csparse 3 3 '(1 3 9 1 4 16 1 7 49)))) ;; same for disk-hnf
    (hit-with-disk-hnf a)
    (hnf-f a 0)
    (assert (equalp a (input-csparse 3 3 '(4 0 1 0 3 1 0 0 1)))))
  (do ((a 1 (1+ a)))
      ((> a 3))
    (do ((b 0 (1+ b)))
	((= b a))
      (do ((d 1 (1+ d)))
	  ((> d 3))
	(dotimes (w 4)
	  (dotimes (x 4)
	    (dotimes (y 4)
	      (dotimes (z 4)
		(when (= (abs (- (* w z) (* x y))) 1)
		  (let ((aa (m-mult (input-csparse 2 2 (list a b 0 d))
				    (input-csparse 2 2 (list w x y z)))))
		    (integrity-check aa
				     :message "abd-wxyz test, after m-mult, before hnf-f: ")
		    (hnf-f aa)
		    (integrity-check aa
				     :message "abd-wxyz test, after hnf-f: ")
		    (assert (equalp (input-csparse 2 2 (list a b 0 d))
				    aa)
			()
		      "GL(2) HNF test failed.~%Given:~%~A~%times~A~%whose product is:~%~A~%The HNF should match the first given:~%~A"
		      (input-csparse 2 2 (list a b 0 d))
		      (input-csparse 2 2 (list w x y z))
		      (m-mult (input-csparse 2 2 (list a b 0 d))
			      (input-csparse 2 2 (list w x y z)))
		      aa))))))))))
  (let ((p-list '()))
    (block first-few-primes
      (let ((ct 0))
	(do-mset (p *primes*)
	  (push p p-list)
	  (incf ct)
	  (when (= ct 30)
	    (return-from first-few-primes)))))
    ;; Three tests of disk-hnf.
    #|
    ;; Skip in the release because rename-file is buggy on CLisp.
    (dolist (width '(4 5 10))
      (let ((a (input-csparse 3 10 (reverse p-list)))
	    (*disk-hnf-width* #'(lambda (m0) (declare (ignore m0)) width)))
	(hit-with-disk-hnf a)
	(integrity-check a)
	;; Up to sign, first three cols should be
	;; 1  0 0
	;; 0  1 0
	;; 0 -1 2
	(let ((d (csparse-move-to-dense a 0 3 0 10)))
	  (dotimes-f (i 3)
	    (dotimes-f (j 10)
	      (assert (= (abs (aref d i j))
			 (if (= i 0)
			     (if (= j 0) 1 0)
			   (if (= i 1)
			       (if (= j 1) 1 0)
			     (if (= i 2)
				 (if (= j 1) 1 (if (= j 2) 2 0))))))
		  ()
		"Messed up HNF of 3 by 10 matrix of first 30 primes."))))))
		|#
    ;; Test the same matrix for minor trick.
    (do ((minor-width 1 (1+ minor-width)))
	((> minor-width 4))
      (let ((*allow-minor-trick* t)
	    (*minor-trick-threshold* 0.0)
	    (*minor-trick-col-func* #'(lambda (m0)
					(declare (ignore m0))
					minor-width))
	    (a (input-csparse 3 10 (reverse p-list))))
	(let ((b (make-snf a t t nil)))
	  (integrity-check b)
	  (assert (= (rank b) 3))
	  (assert (= (num-units b) 2))
	  (assert (equal (mapcar #'sp-integer-value (mapcar #'sp-pretty-associate (torsion b)))
			 '(2)))))))

  ;; Tests for csparse arithmetic.
  (dotimes (i0 3)
    (dotimes (j0 3)
      (do ((s 0 (1+ s)))
	  ((not (and (<= (+ i0 s) 3) (<= (+ j0 s) 3))))
	(let ((input '()))
	  (dotimes (i1 3)
	    (dotimes (j1 3)
	      (push (if (and (<= i0 i1)
			     (<= j0 j1)
			     (= (- i1 i0) (- j1 j0))
			     (< (- i1 i0) s))
			1
		      0)
		    input)))
	  (assert (equalp (make-zero-and-id 3 3 i0 j0 s)
			  (input-csparse 3 3 (nreverse input))))))))
  (labels ((i22 (lyst)
	     (input-csparse 2 2 lyst))
	   (i21 (lyst)
	     (input-csparse 2 1 lyst)))
    (let ((pp (i22 '(5 -13 -7 19))))
      ;;  5 -13
      ;; -7  19
      (assert (equalp (m-add pp pp) (i22 '(10 -26 -14 38))))
      (assert (equalp (m-negate pp) (i22 '(-5 13 7 -19))))
      (assert (equalp (m-mult pp pp) (i22 '(116 -312 -168 452))))
      (assert (equalp (m-subtract (m-mult pp pp) pp)
		      (i22 '(111 -299 -161 433))))
      (assert (equalp (m-mult (make-perm2 0 1) (csparse-copy pp))
		      (i22 '(-7 19 5 -13))))
      (assert (equalp (m-mult (csparse-copy pp) (make-perm2 0 1))
		      (i22 '(-13 5 19 -7))))
      (let ((p01 (make-perm (make-array 2 :initial-contents '(1 0)))))
	(assert (equalp (m-mult p01 (csparse-copy pp))
			(i22 '(-7 19 5 -13))))
	(assert (equalp (m-mult (csparse-copy pp) p01)
			(i22 '(-13 5 19 -7)))))
      (assert (equalp (m-mult (make-transv 1 '(0 . 1)) (csparse-copy pp))
		      (i22 '(-2 6 -7 19))))
      (assert (equalp (m-mult (make-transv 0 '(1 . 1)) (csparse-copy pp))
		      (i22 '(5 -13 -2 6))))
      (assert (equalp (m-mult (csparse-copy pp) (make-transv 1 '(0 . 1)))
		      (i22 '(5 -8 -7 12))))
      (assert (equalp (m-mult (csparse-copy pp) (make-transv 0 '(1 . 1)))
		      (i22 '(-8 -13 12 19))))
      (assert (equalp (m-transpose (csparse-copy pp)) (i22 '(5 -7 -13 19))))
      (let ((pps (make-snf pp)))
	;; To repeat, pp is
	;;  5 -13
	;; -7  19
	(integrity-check pps)
	(assert (= (rank pps) 2))
	(assert (= (num-units pps) 1))
	(assert (equal (mapcar #'sp-integer-value (mapcar #'sp-pretty-associate (torsion pps)))
		       '(4)))
	(assert (m-image-contained-in-image (i22 '(13 5 -19 -7)) pps))
	(assert (equalp (hnf (m-inverse-image (i22 '(13 5 -19 -7)) pps))
			(i22 '(1 0 0 1))))
	(assert (m-image-contained-in-image (i22 '(-26 0 38 0)) pps))
	(assert (equalp (hnf (m-inverse-image (i21 '(-26 38)) pps))
			(i21 '(0 2))))
	(assert (m-image-contained-in-image (i22 '(-29 63 43 -89)) pps))
	(assert (equalp (hnf (m-inverse-image (i21 '(-29 43)) pps))
			(i21 '(2 3))))
	(assert (equalp (hnf (m-inverse-image (i21 '(63 -89)) pps))
			(i21 '(-10 1))))
	(do ((k 60 (1+ k)))
	    ((= k 65))
	  (unless (= k 63)
	    (assert (not (m-image-contained-in-image (i22 (list -29 k 43 -89))
						     pps))))))
      (let ((pps (make-snf pp t t nil t)))
	;; Same as previous test with pps, but writes P's and Q's to disk.
	(integrity-check pps)
	(assert (= (rank pps) 2))
	(assert (= (num-units pps) 1))
	(assert (equal (mapcar #'sp-integer-value (mapcar #'sp-pretty-associate (torsion pps)))
		       '(4)))
	(assert (m-image-contained-in-image (i22 '(13 5 -19 -7)) pps))
	(assert (equalp (hnf (m-inverse-image (i22 '(13 5 -19 -7)) pps))
			(i22 '(1 0 0 1))))
	(assert (m-image-contained-in-image (i22 '(-26 0 38 0)) pps))
	(assert (equalp (hnf (m-inverse-image (i21 '(-26 38)) pps))
			(i21 '(0 2))))
	(assert (m-image-contained-in-image (i22 '(-29 63 43 -89)) pps))
	(assert (equalp (hnf (m-inverse-image (i21 '(-29 43)) pps))
			(i21 '(2 3))))
	(assert (equalp (hnf (m-inverse-image (i21 '(63 -89)) pps))
			(i21 '(-10 1))))
	(do ((k 60 (1+ k)))
	    ((= k 65))
	  (unless (= k 63)
	    (assert (not (m-image-contained-in-image (i22 (list -29 k 43 -89))
						     pps))))))
      (let ((qq (make-csparse-zero 2 2)))
	(csparse-set qq (make-sp-z 0 5) 0)
	(csparse-set qq (make-sp-z 0 -13) 1)
	(csparse-set qq (make-sp-z 1 -7) 0)
	(csparse-set qq (make-sp-z 1 19) 1)
	(assert (equalp pp qq))))
    (dotimes (a 2)
      (dotimes (b 2)
	(dotimes (c 2)
	  (dotimes (d 2)
	    (assert (equalp (m-transpose (i22 (list a b c d)))
			    (i22 (list a c b d)))))))))

  ;; perm times csparse, and csparse times perm.  3 by 3.
  (dolist (i0 '(0 1 2))
    (dolist (i1 (remove i0 '(0 1 2)))
      (dolist (i2 (remove i1 (remove i0 '(0 1 2))))
	(let* ((arr (make-array 3 :initial-contents (list i0 i1 i2)))
	       (P (make-perm arr)))
	  (dolist (k0 '(0 1 2))
	    (dolist (k1 (remove k0 '(0 1 2)))
	      (dolist (k2 (remove k1 (remove k0 '(0 1 2))))
		(let ((A (make-csparse-zero 3 3)))
		  (csparse-set A (make-sp-z k0 1) 0)
		  (csparse-set A (make-sp-z k1 1) 1)
		  (csparse-set A (make-sp-z k2 1) 2)
		  (m-mult P A)
		  (with-csparse-slots (cols) A
		    (dotimes (j 3)
		      (assert (= (length (svref cols j)) 1) ())
		      (let ((ea (csparse-get A
					     (svref arr (if (= j 0)
							    k0
							  (if (= j 1)
							      k1
							    k2)))
					     j)))
			(assert ea ())
			(assert (= (sp-integer-value ea) 1) ())))))
		(let ((B (make-csparse-zero 3 3)))
		  (csparse-set B (make-sp-z k0 1) 0)
		  (csparse-set B (make-sp-z k1 1) 1)
		  (csparse-set B (make-sp-z k2 1) 2)
		  (m-mult B P)
		  (with-csparse-slots (cols) B
		    (dotimes (j 3)
		      (assert (= (length (svref cols j)) 1) ())
		      (let* ((i (svref arr j))
			     (eb (csparse-get B
					      (if (= i 0)
						  k0
						(if (= i 1)
						    k1
						  k2))
					      j)))
			(assert eb ())
			(assert (= (sp-integer-value eb) 1) ()))))))))))))

  (dotimes (a 3)
    (dotimes (b 3)
      (dotimes (c 3)
	(dotimes (d 3)
	  (dotimes (e 3)
	    (dotimes (f 3)
	      (dotimes (g 3)
		(let ((args (mapcar #'1- (list a b c d e f g))))
		  (integrity-check (make-snf (input-csparse 3 3 args)))
		  (integrity-check (make-snf (input-csparse 3 5 args)))
		  (integrity-check (make-snf (input-csparse 5 3 args)))))))))))
  (let ((pp (input-csparse 4 4 '(1 0 0 0 1 1 0 0 1 1 1 0 1 1 1 1))))
    (assert (= (sparsity pp 0) 10/16))
    ;; (assert (= (sparsity pp 1) 6/9))
    ;; (= (/ 2.0 3.0) 2/3) is true in Allegro 6.2 but not in 7.0
    (assert (= (round (* (sparsity pp 1) 9)) 6))
    (assert (= (sparsity pp 2) 3/4))
    (assert (= (sparsity pp 3) 1)))

  ;; More tests of m-inverse-image.
  (let ((chess (input-csparse 4 4 '(2 1 0 0 ;; the 4D checkerboard lattice
				    0 1 1 0
				    0 0 0 1
				    0 0 1 1))))
    (dotimes (nuqq 4)
      (do ((rqq nuqq (1+ rqq)))
	  ((= rqq 4))
	(let ((qq (make-csparse-zero 4 4)))
	  (dotimes (i 4)
	    (if (< i nuqq)
		(csparse-set qq (make-sp-z i 1) i)
	      (when (< i rqq)
		(csparse-set qq (make-sp-z i 2) i))))
	  (let* ((ans1 (m-inverse-image chess (make-snf qq)))
		 (ans2 (hnf ans1)))
	    (with-csparse-slots (m n) ans2
	      (assert (= m n 4))
	      (let ((ans (csparse-move-to-dense ans2 0 4 0 4)))
		(labels ((ei-p (i j)
			   "Col j is e_i."
			   (dotimes (i0 4 t)
			     (unless (= (aref ans i0 j) (if (= i0 i) 1 0))
			       (return nil))))
			 (two-ei-p (i j)
			   "Col j is 2 * e_i."
			   (dotimes (i0 4 t)
			     (unless (= (aref ans i0 j) (if (= i0 i) 2 0))
			       (return nil))))
			 (chess-p (j)
			   "Col j is as in (hnf chess)."
			   (if (= j 0)
			       (two-ei-p 0 0)
			     (dotimes (i 4 t)
			       (unless (if (member i (list 0 j) :test #'=)
					   (= (aref ans i j) 1)
					 (zerop (aref ans i j)))
				 (return nil))))))
		  (dotimes (k 4)
		    (if (< k nuqq)
			(assert (chess-p k) ()
			  "Col ~D is not as in (hnf chess)." k)
		      (assert (ei-p k k) ()
			"Col ~D is not e_~D." k k)))))))))))

  ;; Tests for from- and to-dense-matrix
  (dotimes (a 2)
    (dotimes (b 2)
      (dotimes (c 2)
	(dotimes (d 2)
	  (dotimes (e 2)
	    (dotimes (f 2)
	      (dotimes (g 2)
		(dotimes (h 2)
		  (dotimes (i 2)
		    (let ((aa (input-csparse 3 3 (list a b c d e f g h i))))
		      (dotimes (i0 2)
			(dotimes (j0 2)
			  (let ((i1 (+ i0 2))
				(j1 (+ j0 2))
				(ca (csparse-copy aa)))
			    (let ((da (csparse-move-to-dense ca i0 i1 j0 j1)))
			      (csparse-move-from-dense ca da i0 i1 j0 j1)
			      (assert (equalp aa ca))))))))))))))))

  ;; Tests for jac with LLL.
  (let ((sz 20))
    (let ((*verbose* nil)
	  (*lll-next-try* (floor sz 4)))
      (let ((a (make-csparse-zero sz sz)))
	;; Let a be unipotent lower-triangular with random entries below
	;; the diagonal.
	(dotimes (i sz)
	  (csparse-set a (make-sp-z i 1) i)
	  (dotimes (j i)
	    (csparse-set a (make-sp-z i (random 1000000)) j)))
	(let ((a-snf (make-snf a nil nil)))
	  (assert (= (rank a-snf) sz))
	  (assert (= (num-units a-snf) sz))
	  (assert (endp (torsion a-snf)))))))

  ;; Tests for block triangularization.  'des' means Duff, Erisman and
  ;; Reid, _Direct Methods for Sparse Matrices_.  The rest of the
  ;; variable name is a reference to the example.
  (labels ((des62-test (a example-name ct-guess &key (p-should-be-id nil))
	     (let* ((aa (csparse-copy a))
		    (P (permute-rows-onto-diag aa)))
	       (when p-should-be-id
		 (assert (m-id-p P) ()
		   "DES ~A got unexpected non-id P: ~A"
		   example-name P))
	       (assert (= (count-on-diagonal aa) ct-guess) ()
		 "DES ~A got wrong count [/= ~D] on diagonal:~&~A"
		 example-name ct-guess aa)
	       (m-mult P aa)
	       (assert (equalp a aa) ()
		 "DES ~A is wrong when multiplied back.~&Old:~&~A~&New:~&~A"
		 example-name a aa))))
    (des62-test (input-csparse 7 7 '(1 0 0 1 0 0 0
				     0 1 0 0 0 1 0
				     0 0 1 0 0 0 1
				     1 0 0 1 0 0 0
				     0 1 0 0 1 0 0
				     0 0 0 0 0 0 1
				     0 0 0 0 0 1 0))
		"Fig 6.2.1" 7)
    (des62-test (input-csparse 7 7 '(1 0 0 0 0 1 0
				     0 1 0 0 0 0 1
				     1 0 1 0 0 0 0
				     0 0 0 1 0 0 0
				     0 0 0 0 1 0 0
				     0 1 0 0 0 0 0
				     1 0 0 0 0 0 1))
		"Fig 6.2.2" 7)
    (des62-test (input-csparse 6 6 '(1 0 0 0 0 1
				     0 1 0 0 0 0
				     0 0 1 0 0 0
				     0 0 0 1 0 0
				     0 0 0 0 1 0
				     0 1 0 0 0 0))
		"Fig 6.2.3" 5 :p-should-be-id t)
    (des62-test (input-csparse 8 8 '(1 0 0 0 0 0 0 1
				     0 1 0 0 0 0 0 0
				     1 0 1 0 0 0 0 0
				     0 0 0 1 0 1 0 0
				     0 0 0 0 1 0 0 0
				     0 0 1 0 0 1 0 0
				     0 0 0 0 0 0 1 0
				     0 0 0 1 0 0 0 0))
		"Fig 6.2.4" 8)
    (des62-test (input-csparse 6 6 '(1 0 0 0 0 0
				     0 1 0 0 0 1
				     0 0 1 0 0 0
				     0 1 0 1 0 0
				     0 0 0 0 1 0
				     0 0 0 1 0 0))
		"Fig 6.3.1" 6)
    (des62-test (input-csparse 6 6 '(1 0 0 0 0 1
				     0 1 0 0 0 0
				     0 0 1 0 0 1
				     0 0 0 1 0 0
				     0 0 0 0 1 0
				     0 0 1 0 0 0))
		"Fig 6.3.2" 6)
    (des62-test (input-csparse 8 8 '(1 0 0 0 0 0 0 1
				     0 1 0 0 0 0 0 0
				     1 0 1 0 1 0 0 0
				     0 0 0 1 0 0 0 0
				     0 1 1 0 1 0 0 0
				     0 0 0 0 1 1 0 0
				     0 0 0 0 0 0 1 0
				     0 0 0 0 0 1 0 0))
		"Fig 6.3.3" 8)
    (des62-test (input-csparse 8 8 '(1 0 0 0 0 0 0 1
				     0 1 0 0 0 0 0 0
				     1 0 1 0 1 0 0 0
				     0 0 0 1 0 0 0 0
				     0 1 1 0 1 0 0 0
				     0 0 1 0 0 1 0 0
				     0 0 0 0 0 0 1 0
				     0 0 0 0 0 1 0 0))
		"Fig 6.3.4" 8))

  ;; Tests for csparse-move-to-pari.
  (do ((a 0 (1+ a)))
      ((= a 5))
    (do ((b (1+ a) (1+ b)))
	((= b 5))
      (let ((aa (make-csparse-zero 2 5)))
	(csparse-set aa (make-sp-z 0 2) a)
	(csparse-set aa (make-sp-z 0 1) b)
	(csparse-set aa (make-sp-z 1 3) b)
	(multiple-value-bind (i0 n0 fc) (csparse-move-to-pari aa 0 5)
	  (assert (= i0 0) () "i0 /= 0 in csparse-move-to-pari test.")
	  (assert (= n0 2) () "n0 /= 2 in csparse-move-to-pari test.")
	  (let ((filename (format nil "pari~D.txt" fc)))
	    (with-open-file (s filename)
	      (assert (equalp (read-line s) "[2, 1; 0, 3]") ()
		"csparse-move-to-pari wrote the wrong line to ~A." filename)
	      (assert (null (read s nil)) ()
		"~A had a second line." filename))
	    (delete-file filename))))))

  ;; Tests for dense-matrix-mod-p: row-reduction and kernels.
  (labels ((sl23-test (aa-echelon)
	     "Give it a dense-matrix-mod-p that's a 2-by-n echelon
            matrix mod 3 with entries in {0,1,2}.  We multiply it
            on the left by all possible matrices in SL(2,3), then
            put the result back to echelon form and see if it's
            the same.  aa-echelon itself is unchanged."
	     (let ((a (mat aa-echelon))
		   (n (m-num-cols aa-echelon))
		   (p (dense-matrix-mod-p-p aa-echelon)))
	       (assert (= (m-num-rows aa-echelon) 2)) ;; m
	       (assert (= (length a) (* 2 n)))
	       (assert (= p 3))
	       (dotimes-f (w 3)
		 (dotimes-f (x 3)
		   (dotimes-f (y 3)
		     (dotimes-f (z 3)
		       (when (= 1 (rem (- (* w z) (* x y)) 3))
			 (let* ((bb (make-dense-matrix-mod-p-zero 2 n p))
				(b (dense-matrix-mod-p-mat bb)))
			   (dotimes-f (j n)
			     (setf (aref b j) ;; row 0, col j
			       (rem (+ (* w (aref a j))
				       (* x (aref a (+ n j)))) p))
			     (setf (aref b (+ n j)) ;; row 1, col j
			       (rem (+ (* y (aref a j))
				       (* z (aref a (+ n j)))) p)))
			   (row-reduce-mod-p bb)
			   (dotimes-f (k (length b))
			     (setf (aref b k) (mod (aref b k) 3)))
			   (assert (equalp aa-echelon bb) ()
			     "Row-reduce-mod-p failed: input~&~A~&output~&~A~&"
			     aa-echelon bb))))))))))
    (let* ((aa (make-dense-matrix-mod-p-zero 2 2 3))
	   (a (dense-matrix-mod-p-mat aa)))
      (dotimes-f (d 2)
	(setf (aref a 0) 1 (aref a 1) 0
	      (aref a 2) 0 (aref a 3) d)
	(sl23-test aa)
	(let ((kk (m-ker aa)))
	  (assert (= (m-num-rows kk) 2) () "Ker has wrong height.")
	  (if (= d 1)
	      (assert (zerop (m-num-cols kk)) () "Ker of 1 0 / 0 1 is not zero.")
	    (with-dense-matrix-mod-p-slots ((kk-a mat)) kk
	      (assert (= (m-num-cols kk) 1) ()
		"Ker of 1 0 / 0 0 is not of dim 1.")
	      (assert (and (= 0 (aref kk-a 0)) ;; row 0, col 0
			   (/= 0 (mod (aref kk-a 1) 3))) ;; row 1, col 0
		  () "Ker of 1 0 / 0 0 is not 0 / * ."))))))
    (let* ((aa (make-dense-matrix-mod-p-zero 2 3 3))
	   (a (dense-matrix-mod-p-mat aa)))
      (setf (aref a 0) 1 (aref a 1) 0 (aref a 2) 0
	    (aref a 3) 0 (aref a 4) 0 (aref a 5) 1)
      (sl23-test aa)
      (let ((kk (m-ker aa)))
	(with-dense-matrix-mod-p-slots ((kk-a mat)) kk
	  (assert (= (m-num-rows kk) 3) ()
	    "Ker of 1 0 0 / 0 0 1 has wrong height.")
	  (assert (= (m-num-cols kk) 1) ()
	    "Ker of 1 0 0 / 0 0 1 is not of dim 1.")
	  (assert (and (= 0 (aref kk-a 0))
		       (/= 0 (mod (aref kk-a 1) 3))
		       (= 0 (aref kk-a 2)))
	      () "Ker of 1 0 0 / 0 0 1 is not 0 / * / 0."))))
    (let* ((aa (make-dense-matrix-mod-p-zero 2 3 3))
	   (a (dense-matrix-mod-p-mat aa)))
      (dotimes-f (c 3)
	(dotimes-f (f 3)
	  (setf (aref a 0) 1 (aref a 1) 0 (aref a 2) c
		(aref a 3) 0 (aref a 4) 1 (aref a 5) f)
	  (sl23-test aa)
	  (let ((kk (m-ker aa)))
	    (with-dense-matrix-mod-p-slots ((kk-a mat)) kk
	      (assert (= (m-num-rows kk) 3) ()
		"Ker of 1 0 c / 0 1 f has wrong height.")
	      (assert (= (m-num-cols kk) 1) ()
		"Ker of 1 0 c / 0 1 f is not of dim 1.")
	      (assert (or
		       (and (= c (mod (aref kk-a 0) 3))
			    (= f (mod (aref kk-a 1) 3))
			    (= 2 (mod (aref kk-a 2) 3)))
		       (and (= (if (zerop c) 0 (- 3 c)) (mod (aref kk-a 0) 3))
			    (= (if (zerop f) 0 (- 3 f)) (mod (aref kk-a 1) 3))
			    (= 1 (mod (aref kk-a 2) 3))))
		  () "Ker of 1 0 0 / 0 0 1 is not c / f / -1 up to sign.")))))))

  ;; Tests for nested minor trick.
  (dolist (width '(45 100 255))
    ;; (ceiling n width) is 12, 6, 3 respectively
    (with-open-file (si "test11.lisp" :direction :input)
      (let ((m (read si))
	    (n (read si)))
	(let ((A (make-csparse-zero m n)))
	  (loop
	    (let ((i (read si nil)))
	      (unless i
		(return))
	      (let ((j (read si))
		    (v (read si)))
		(csparse-set A (make-sp-z i v) j))))
	  (let ((*allow-minor-trick* t)
		(*minor-trick-threshold* 0.0)
		(*minor-trick-col-func*
		 (lambda (m0)
		   (declare (ignore m0))
		   width)))
	    (let ((snf-A (make-snf A t t nil t))
		  (message
		   (format nil "Minor trick, test11.lisp, width ~D." width)))
	      (integrity-check snf-A :message message))))))))

;;; ----------------------  Other unit tests  ----------------------

(dolist (p '(2 3 5 12379))
  (let ((fib-polyn (vector 1 (- p 1) (- p 1)))) ;; min polyn of Fibonacci seq
    (dolist (s '(#(0 1 1 2) ;; different subseqs of Fibonacci
		 #(2 3 5 8)
		 #(17 76 93 169))) ;; Fibonacci starting differently
      (unless (and (= p 5) (= (svref s 0) 17)) ;; this one ramifies
	(multiple-value-bind (deg ans) (berlekamp-massey s 2 p)
	  (assert (and (= deg 2)
		       (equalp (subseq ans 0 3) fib-polyn)
		       ;; Don't know if the next line *should* hold.
		       (every #'zerop (subseq ans 3)))))))))

;; Example from the Maple code cited in berlekamp-massey's doc.
;; num = 21 + 83*x + 90*x^2 + 4*x^3
;; den = 1 + 11*x + 23*x^2 + 58*x^3 + 69*x^4
;; Let f be the rational function num/den.  The coefficients of the
;; Taylor polynomial of f form a linearly recurrent sequence with
;; minimal polynomial den.  Let s be the Taylor coefficients of x^0
;; through x^7, modulo 103, as computed by Pari.
(let ((s #(21 58 102 38 45 43 65 68)))
  (multiple-value-bind (deg ans) (berlekamp-massey s 4 103)
    (assert (and (= deg 4)
		 (equalp (subseq ans 0 5) #(1 11 23 58 69))
		 ;; Don't know if the next line *should* hold.
		 (every #'zerop (subseq ans 5))))))

;;; ################# Old commented-out code (various D) #################

;;; Surprisingly, worse than the other version of pivot-markowitz.
;;; Restricting the second loop to j-best-norm was supposed to be the
;;; time-saver, but so many pivots have the same minimal norm that
;;; it's not worth evaluating the norms twice.  In a test on a 3898 by
;;; 13644 matrix over Z (level 24), at least 40% of the columns had an
;;; elt of norm 1 for almost the whole computation.
#|
(defun pivot-markowitz (d corner)
  "A pure Markowitz algorithm for pivoting."
  (declare (type csparse d) (type nnfixnum corner))
  (with-csparse-slots (m n cols) d
    (assert (and (<= 0 corner m) (<= 0 corner n)) ()
      "Index out of bounds: ~D in a ~D-by-~D matrix." corner m n)
    (let ((rlen (first *markowitz-rlen*))
          (clen (first *markowitz-clen*))
	  (best-norm -1)
	  (j-best-norm '()))
      (declare (simple-vector rlen clen) (integer best-norm)
	       (list j-best-norm))
      ;; First sweep: set all row and column lengths.
      (fill rlen -1 :start corner)
      (do ((j corner (1+ j))
	   (clen-j -1 -1))
          ((>= j n))
        (declare (type nnfixnum j) (fixnum clen-j))
        (dolist (ae (the sparse-v (svref cols j)))
          (incf (svref rlen (sp-i ae)))
	  (incf clen-j)
	  (let ((norm (sp-euc-norm ae)))
	    (declare (integer norm))
	    (if (or (= best-norm -1) ;; = +infinity
		    (< norm best-norm))
		(setq best-norm norm j-best-norm (list j))
	      (when (= norm best-norm)
		(unless (= j (the nnfixnum (first j-best-norm)))
		  (push j j-best-norm))))))
	(setf (svref clen j) clen-j))
      (when (and *verbose* (< corner n)
		 (zerop (mod corner 50)))
	(format t "~&cor ~D   norm ~D   frac cols ~5,3F~&"
		corner best-norm
		(float (/ (length j-best-norm) (- n corner)))))
      ;; Second sweep: get best pivot.
      (let ((best-i 0)
            (best-j 0)
            (best-elt nil)
            (best-markow-ct (* (- m corner) (- n corner))))
	(declare (type nnfixnum best-i best-j)
		 (integer best-markow-ct))
        (dolist (j (nreverse j-best-norm)
		  (values best-i best-j best-elt))
          (declare (type nnfixnum j))
          (let ((clen-j (svref clen j)))
	    (declare (type nnfixnum clen-j))
            (dolist (ae (the sparse-v (svref cols j)))
              (let ((norm (sp-euc-norm ae))
                    (markow-ct (* (the nnfixnum (svref rlen (sp-i ae)))
                                  clen-j)))
                (declare (integer norm markow-ct))
                (when (and (= norm best-norm) (< markow-ct best-markow-ct))
                  (setq best-i (sp-i ae) best-j j best-elt ae
                        best-markow-ct markow-ct))))))))))
|#

#|
(defun clean-by-lower-tri (a1 from1 to1 a2 from2 to2)
  "For j2 in [from2,to2), and for j1 in [from1,to1) in order,
alter column j2 of a2 by v1 = column j1 of a1 so as to clean out the
top slot of v1 as much as possible.  This doesn't make sense unless
the j1-range of a1 is lower-triangular; see the function with hnf in
their names, and caveat reductor.  The two a's can be the same, but
don't let the ranges overlap."
  (with-csparse-slots ((m1 m) (n1 n) (cols1 cols)) a1
    (assert (<= 0 from1 to1 n1) (from1 to1)
      "Violated (<= 0 from1 to1 n1).")
    (with-csparse-slots ((m2 m) (n2 n) (cols2 cols)) a2
      (unless (= m1 m2)
	(cerror "Keep going anyway."
		"Different m's: ~D by ~D, versus ~D by ~D." m1 n1 m2 n2))
      (assert (<= 0 from2 to2 n2) (from2 to2)
	"Violated (<= 0 from2 to2 n2).")
      (do ((j2 from2 (1+ j2)))
	  ((= j2 to2))
	(declare (type nnfixnum j2))
	(when (svref cols2 j2)
	  (do ((j1 from1 (1+ j1)))
	      ((= j1 to1))
	    (declare (type nnfixnum j1))
	    (let ((v1 (svref cols1 j1)))
	      (declare (type sparse-v v1))
	      (when v1
		(let* ((e1 (first v1))
		       (i1 (sp-i e1)))
		  (declare (type nnfixnum i1))
		  (let ((e2 (v-get (svref cols2 j2) i1)))
		    (when e2
		      (let ((q (sp-neg-closest-quotient e2 e1)))
			(v-alter-f (svref cols2 j2) q v1)))))))))))))
|#

#|
(defun hit-with-disk-hnf (a min-j file-counter)
  "Removes all columns j >= min-j from the csparse a, runs
do-disk-hnf on these columns, and puts the result back into A.
Returns the altered A."
  (declare (type csparse a) (type nnfixnum min-j) (integer file-counter))
  (when (< file-counter 0)
    (cerror "Keep going."
	    "File counter is negative.  Usually hit-with-disk-hnf is only run~&for snf's with p-q-to-file true."))
  (let ((stem (format nil "hnf~Dc" file-counter))
	(ij-list '()))
    (with-slots (n cols) a
      (let ((v (make-array 0 :adjustable t :fill-pointer t)))
	(do ((j min-j (1+ j)))
	    ((>= j n))
	  (declare (type nnfixnum j))
	  (let ((col (svref cols j)))
	    (declare (type sparse-v col))
	    (when col
	      (let ((ilj (list (sp-i (first col)) (length col) j)))
		(vector-push-extend ilj v)))
	    (disk-hnf-write col stem j))
	  (setq (svref cols j) '()))
	;; It may(??) be useful here to call a full garbage collection.
	(sortf v #'(lambda (ilj1 ilj2)
			    (declare (list ilj1 ilj2))
			    (let ((i1 (first ilj1))
				  (i2 (first ilj2)))
			      (declare (type nnfixnum i1 i2))
			      (if (< i1 i2)
				  t
				(if (> i1 i2)
				    nil
				  (< (the integer (second ilj1))
				     (the integer (second ilj2))))))))
	(till (zerop (fill-pointer v))
	  (let ((ilj (vector-pop v)))
	    (declare (list ilj))
	    (push (cons (first ilj) (third ilj)) ij-list)))) Main HNF
      ;; loop.
      (do-disk-hnf stem ij-list)
      ;; Copy result back to cols, and clean up files.
      (do ((j min-j (1+ j))
	   (k min-j))
	  ((>= j n))
	(declare (type nnfixnum j k))
	(let ((col (disk-hnf-read stem j)))
	  (declare (type sparse-v col))
	  (when col
	    (setf (svref cols k) col)
	    (incf k)))
	(disk-hnf-delete stem j)))))

(defun do-disk-hnf (stem ij-list)
  (declare (string stem) (list ij-list))
  (let ((j-done '())
	(ct 0))
    (declare (list j-done) (fixnum ct))
    (till (endp ij-list)
      (let ((i (car (first ij-list)))
	    (j (cdr (first ij-list))))
	(declare (type nnfixnum i j))
	(when (and *verbose* (zerop (mod ct 1000)))
	  (format t "~&    disk-hnf ct=~D i=~D ~A~&" ct i (time-stamp)))
	(incf ct)
	(let ((v (disk-hnf-read stem j)))
	  (declare (type sparse-v v))
	  (assert v () "A zero v got in.")
	  (assert (= i (sp-i (first v))) () "v's i's out of synch.")
	  (if (or (endp (rest ij-list))
		  (> (the nnfixnum (car (second ij-list))) i))
	      (progn
		(dolist (j1 j-done)
		  (declare (type nnfixnum j1))
		  (let* ((w (disk-hnf-read stem j1))
			 (wi (v-get w i)))
		    (declare (type sparse-v w))
		    (when wi
		      (v-alter-f w (sp-neg-closest-quotient wi (first v)) v)
		      (disk-hnf-write w stem j1))))
		(push (cdr (pop ij-list)) j-done))
	    (let* ((k (cdr (second ij-list)))
		   (w (disk-hnf-read stem k)))
	      (declare (type nnfixnum k) (type sparse-v w))
	      (assert w () "A zero w got in.")
	      (assert (= i (sp-i (first w))) () "w's i's out of synch.")
	      (multiple-value-bind (new-v new-w) (disk-hnf-2-col-step v w)
		(declare (type sparse-v new-v new-w))
		;; new-v's first entry is still at i; new-w's lower
		(unless (equalp v new-v)
		  (disk-hnf-write new-v stem j))
		(disk-hnf-write new-w stem k)
		(rplacd ij-list (cddr ij-list)) ;; cut out (i . k)
		(when new-w
		  (let* ((newi (sp-i (first new-w)))
			 (newi-k (cons newi k)))
		    (declare (type nnfixnum newi))
		    (with-splicer ij-list
		      (till (or (splicer-endp)
				;; >, not >=, since new-w is(?) relatively
				;; dense, and we want to handle dense ones
				;; after the sparse ones
				(> (the nnfixnum (car (splicer-read))) newi))
			(splicer-fwd))
		      (splicer-insert newi-k))))))))))))
|#

;;; Overwrites a with [write me].  The gamble is that, when m is much
;;; smaller than n, we can reduce a0 when we couldn't reduce A.
;;; Returns a list of P's, in the correct order so you can append them
;;; to the end of the list of the caller's P's.
#|
(defun hit-with-minor-trick (a corner fc)
  (declare (type csparse a) (type nnfixnum corner) (integer fc))
  (with-csparse-slots (m n cols) a
    (assert (and (<= 0 corner m) (< m n)) ()
      "Dim check failed: 0 <= ~D <= ~D < ~D" corner m n)
    (when *verbose*
      (format t "~&>>>>Starting minor trick at row ~D ~A~&"
	      corner (time-stamp)))
    ;; Randomize the columns to get a high-rank minor.
    (dotimes-f (ran-ct n)
      (let ((j1 (+ corner (random (- n corner 1)))))
	(let ((j2 (+ j1 1 (random (- n j1 1)))))
	  (swap-cols a j1 j2))))
    (when *verbose*
      (format t "~&>>>>Minor trick finished randomizing ~A~&" (time-stamp)))
    ;; Let a0 be the square submatrix from (corner,corner) to (m,m).
    ;; Delete this part from A.
    (let ((filename (minor-trick-filename fc))
	  (a0 (let ((m0 (- m corner)))
		(declare (type nnfixnum m0))
		(make-csparse-zero m0 m0))))
      (with-csparse-slots ((cols0 cols)) a0
        (do ((j corner (1+ j))
	     (j0 0 (1+ j0)))
	    ((= j m))
	  (declare (type nnfixnum j j0))
	  (let ((col (svref cols j))
		(col0 '()))
	    (declare (type sparse-v col col0))
	    (unless (endp col)
	      (assert (>= (sp-i (first col)) corner) ()
		"a wasn't zero in NE block defined by corner = ~D" corner)
	      (dolist (e col)
		(push (make-sp (- (sp-i e) corner) (sp-v e)) col0)))
	    (setf (svref cols0 j0) (nreverse col0)
		  (svref cols j) '()))))
	;; Dump the right-hand part of a to disk.
	(with-open-file (s filename :direction :output :if-exists :supersede)
	  (do ((j m (1+ j)))
	      ((= j n))
	    (declare (type nnfixnum j))
	    (let ((v (svref cols j)))
	      (declare (type sparse-v v))
	      (when v
		(format-flat s "~S" v)
		(setf (svref cols j) '())))))
	;; Reduce a0 completely.
	(let ((snf0 (make-snf a0 t nil t nil))
	      (j-ct corner))
	  (declare (type nnfixnum j-ct))
	  ;; Paste back into a the reduced (diagonal) part of a0.
	  (with-csparse-slots ((d0cols cols)) (slot-value snf0 'd)
	    (do ((j corner (1+ j))
		 (j0 0 (1+ j0)))
		((>= j m))
	      (let ((v0 (svref d0cols j0)))
		(declare (type sparse-v v0))
		(when v0
		  (assert (endp (rest v0)) ()
		    "d0 isn't diagonal: some col len > 1")
		  (assert (= j0 (sp-i (first v0))) ()
		    "d0 has an off-diagonal entry")
		  (assert (= j-ct j) ()
		    ;; whether v0's are all non-zero follwed by all zero
		    "Pasting d0 into d messes up the diagonal.")
		  (setf (svref cols j-ct)
		    (list (make-sp j (sp-v (first v0)))))
		  (incf j-ct)))))
	  ;; Read in the cols from disk, change coords appropriately
	  ;; by the P's from a0, and paste them back.
	  (let ((pinvs '())
		(nu (+ corner (num-units snf0))))
	    (declare (list pinvs) (type nnfixnum nu))
	    (dolist (p (slot-value snf0 'p-list))
	      (push (m-inverse (m-translate p corner)) pinvs))
	    (setq pinvs (nreverse pinvs)
		  a0 nil snf0 nil) ;; no longer needed
	    (when *verbose*
	      (format t "~&>>>>Minor trick added diagonal 1's up to row ~D~&" nu)
	      (format t "~&>>>>Minor trick altering cols ~A~&" (time-stamp)))
	    (with-open-file (s filename)
	      (let ((oo (make-csparse-zero m 1)))
		(declare (type csparse oo))
		(loop
		  (let ((v (read s nil)))
		    (declare (type sparse-v v))
		    (unless v
		      (return))
		    (setf (svref (csparse-cols oo) 0) v)
		    (dolist (pinv pinvs)
		      (m-mult pinv oo))
		    (setq v (svref (csparse-cols oo) 0))
		    (till (or (endp v) (>= (sp-i (first v)) nu))
		      (pop v))
		    ;; July 3, 2006: in the range nu <= i < rank,
		    ;; ought to mod the entries out by the torsion.
		    ;; Compare the other uses of the variable oo.
		    (when v
		      (setf (svref cols j-ct) v)
		      (incf j-ct))))))
	    (delete-file filename)
	    ;; We're done with A.  Return the values.
	    (let ((ps '()))
	      (declare (list ps))
	      (till (endp pinvs)
		(push (m-inverse (pop pinvs)) ps))
	      (when *verbose*
		(format t "~&>>>>Ending minor trick ~A~&" (time-stamp)))
	      (values nu (nreverse ps))))))))

(defun units-so-far-p (d cor)
  "Returns true if, for columns j in [0,cor), d is a diagonal matrix
of units.  Offers a continuable error, then returns false, if
it finds a non-unit on the diagonal.  Gives a fatal error if it's not
even diagonal."
  (declare (type csparse d) (type nnfixnum cor))
  (with-csparse-slots (m n cols) d
    (assert (<= 0 cor (min m n)) () "Dim mismatch.")
    (dotimes-f (j cor t)
      (let ((colj (svref cols j)))
	(declare (type sparse-v colj))
	(assert (and (not (endp colj))
		     (endp (rest colj))
		     (= j (sp-i (first colj)))) ()
	  "d is not diagonal.")
	(unless (sp-unitp (first colj))
	  (cerror "Keep going."
		  "d has a non-unit on the diagonal at index ~D out of ~D."
		  j cor)
	  (return-from units-so-far-p nil))))))
|#

#|
  (let ((p-list-from-block-block '()))
    (with-csparse-slots (m n) mat ;; "block + disk-hnf", July 2006
      (when (and (not use-q) destructive-p (<= 1 m n))
	(when *verbose*
	  (format t "~&Starting ~D by ~D block-triangularize ~A"
		  m n (time-stamp)))
	(let ((n1 0) ;; widest strip will be n1-left <= j < (n1-left + n1)
	      (n1-left 0))
	  (multiple-value-bind (size-list bt-p-list bt-q-list) (block-triangularize mat)
	    (declare (list size-list bt-p-list) (ignore bt-q-list))
            (assert nil () "Edit this code: bt-p-list is now a perm, not a list.")
	    (when *verbose*
	      (format t "~&Ending block-triangularize ~A" (time-stamp)))
	    (setq p-list-from-block-block
	      (nconc p-list-from-block-block bt-p-list))
	    (when *verbose*
	      (format t "~&Before jac on ~D by ~D, have ~D triangular block~:P whose sizes [omitting 1's]~&are ~A"
		      m n (length size-list) (remove 1 size-list)))
	    (let ((size-accum 0)) ;; running sum of sizes
	      (dolist (size size-list) ;; find widest strip
		(when (> size n1)
		  (setq n1 size
			n1-left size-accum))
		(incf size-accum size))))
	  (let ((n1-right (+ n1-left n1)))
	    (when *verbose*
	      (format t "~&Running disk-hnf before main jac on widest strip ~D" n1))
	    (hit-with-disk-hnf mat :start n1-left :end n1-right)
	    (when *verbose*
	      (format t "~&Using strip to clean left ~D columns. ~A"
		      n1-left (time-stamp)))
	    (clean-by-lower-tri mat n1-left n1-right mat 0 n1-left)
	    (when *verbose*
	      (format t "~&Using strip to clean right ~D columns. ~A"
		      (- n1 n1-right) (time-stamp)))
	    (clean-by-lower-tri mat n1-left n1-right mat n1-right n)))
	(when *verbose*
	  (format t "~&Running disk-hnf before main jac on whole thing."))
	  (hit-with-disk-hnf mat)))
|#

#|
(defun wiedemann-square (A nn b)
  "Given the equation A x = b for square A, either prove the
equation is solvable, or find a dependency among A's columns.  The
point of Wiedemann's methods is that there is no fill-in at all.
  Wiedemann's algorithm requires the underlying domain to be a
finite field.  The implementation here requires F_p.
  Arguments: A is an nn by nn csparse.  In fact, A can be m by n
with m and n >= nn, but it is an error unless all non-zero entries
are in the [0,nn) by [0,nn) square.  b is a column vector
as a sparsev.  It is an error if b has an entry of index >= nn.
  Returns two values:
[.] x, which is either nil or a column nn-vector as a simple-vector.
    If nil, it means A x = b is solvable.  [One could extend the code,
    using the y's in Wiedemann's paper cited below, to return the
    solution.]  If non-nil, it means A x = 0.
[.] p [or 1 in the special case where both A and b are zero].
  We follow Wiedemann, _Solving sparse linear equations over finite
fields_, IEEE Transactions on Information Theory, vol. IT-32, no. 1,
Jan. 1986, pp. 54-62.  This function follows Algorithm 1 of the paper."
  (declare (type csparse A) (fixnum nn) (type sparse-v b))
  (let ((sample-elt (or (first (some #'identity (csparse-cols A))) (first b))))
    (unless sample-elt ;; when A and b are zero
      (return-from wiedemann-square
	(values nil 1)))
    (let ((p (sp-f_p-p sample-elt)))
      (assert p () "The matrix must be defined mod p, not over ~A."
	      (sp-ring-name sample-elt))
      ;; Step 1
      (let ((b0 (make-array nn :initial-element 0))
	    (bk (make-array nn))
	    (uk1 (make-array nn))
	    (dk 0)
	    ;; s, bb, fk1 (a.k.a. cc), and tt are for berlekamp-massey.
	    ;; f is a polynomial, accumulating the product of the fk1's.
	    (s (make-array (* 2 nn)))
	    (bb (make-array (1+ (* 2 nn))))
	    (fk1 (make-array (1+ (* 2 nn))))
	    (tt (make-array (1+ (* 2 nn))))
	    (deg-fk1 -1)
	    (f (make-array (1+ nn) :initial-element 0))
	    (deg-f -1)
	    ;; For a-mult
	    (a-mult-in (make-array nn))
	    (a-mult-out (make-array nn)))
	(declare (fixnum dk deg-fk1))
	(macrolet ((mod-p (x)
		     `(the integer (mod (the integer ,x) (the integer p)))))
	  (labels ((a-mult (init-v)
		     "Copy init-v into a-mult-in, then overwrite a-mult-out with A * a-mult-in."
		     (map-into a-mult-in #'identity init-v)
		     (fill a-mult-out 0)
		     (with-csparse-slots (n cols) A
		       (dotimes-f (j n)
			 (dolist (e (svref cols j))
			   (setf (svref a-mult-out (sp-i e))
			     (mod-p (+ (svref a-mult-out (sp-i e))
				       (* (sp-integer-lift e)
					  (svref a-mult-in j)))))))))
		   (mult-f-by-fk1 ()
		     "Overwrite the polynomial f with f * fk1."
		     (assert nil () "WRITE ME")))
	    ;; Still Step 1
	    (dolist (e b)
	      (setf (svref b0 (sp-i e)) (mod-p (sp-integer-lift e))))
	    (map-into bk #'identity b0)
	    (setf (svref f 0) 1
                  deg-f 0)
	    (loop while (notevery #'zerop bk) do ;; Step 2
		  ;; Step 3
		  (dotimes-f (j nn)
		    (setf (svref uk1 j) (random p)))
		  ;; Step 4
		  (dotimes-f (ell (* 2 (- nn dk)))
		    ;; Put A^ell * bk into a-mult-out.
		    (if (= ell 0)
			(map-into a-mult-out #'identity bk)
		      (a-mult a-mult-out))
		    ;; Put (uk1 dot (A^ell * bk)) into s[ell].
		    (setf (svref s ell) 0)
		    (dotimes-f (i nn)
		      (setf (svref s ell)
			(mod-p (+ (svref s ell)
				  (mod-p (* (svref uk1 i)
					    (svref a-mult-out i))))))))
		  ;; Step 5
		  (setq deg-fk1 (berlekamp-massey s (- nn dk) p :bb bb :cc fk1 :tt tt))
		  ;; For some reason, the coefficients are in the wrong
		  ;; order, and we have to flip them.
		  (do ((jj0 0 (1+ jj0))
		       (jj1 deg-fk1 (1- jj1)))
		      ((>= jj0 jj1))
		    (declare (fixnum jj0 jj1))
		    (psetf (svref fk1 jj0) (svref fk1 jj1)
			   (svref fk1 jj1) (svref fk1 jj0)))
		  ;; Do we have to normalize so fk1[leftmost-nonzero] = 1?
		  ;; STOPPED HERE 11/30/2007.  Will try the simpler
		  ;; probabilistic version with just one f instead of
		  ;; f1*f2*f3*....
		  (mult-f-by-fk1)
		  (when (= (svref fk1 0) 0)
		    ;; Early exit because A is singular.
		    (fill yk 0)
		    (let ((ell0 1)) ;; deg of trailing non-zero term
		      (till (or (> ell0 deg-fk1) (/= (svref fk1 ell0) 0))
			(incf ell0))
		      (do ((ell ell0 (1+ ell)))
			  ((> ell deg-fk1))
			(declare (fixnum ell))
			;; Put A^(ell-ell0) * b0 into a-mult-out.
			(if (= ell ell0)
			    (map-into a-mult-out #'identity b0)
			  (a-mult a-mult-out))
			;; Increment yk with fk1[ell] * a-mult-out.
			(dotimes-f (i nn)
			  (setf (svref yk i)
			    (mod-p (+ (svref yk i)
				      (mod-p (* (svref fk1 ell)
						(svref a-mult-out i))))))))
		      (assert (notevery #'zerop yk) ()
			"In dep case, didn't find a non-zero dep.  deg-fk1 = ~D.  ell0 = ~D.  fk1 = ~A" deg-fk1 ell0 (subseq fk1 0 (1+ deg-fk1))))
		    (map-into a-mult-out #'identity yk)
		    (till (every #'zerop a-mult-out)
		      (a-mult a-mult-out))
		    (return-from wiedemann-square
		      (values a-mult-in nil p)))
		  ;; Step 6
		  (do ((ell 1 (1+ ell)))
		      ((> ell deg-fk1))
		    (declare (fixnum ell))
		    ;; Put A^(ell-1) * bk into a-mult-out.
		    (if (= ell 1)
			(map-into a-mult-out #'identity bk)
		      (a-mult a-mult-out))
		    ;; Increment yk with fk1[ell] * a-mult-out.
		    (dotimes-f (i nn)
		      (setf (svref yk i)
			(mod-p (+ (svref yk i)
				  (mod-p (* (svref fk1 ell)
					    (svref a-mult-out i))))))))
		  (a-mult yk)
		  (dotimes-f (i nn)
		    (setf (svref bk i)
		      (mod-p (+ (svref b0 i) (svref a-mult-out i)))))
		  (incf dk deg-fk1))
	    ;; Step 2 (end)
	    (map-into yk #'(lambda (x) (mod-p (- x))) yk)
	    (values yk t p)))))))
|#
