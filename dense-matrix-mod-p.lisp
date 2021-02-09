(in-package shh2)

(declaim (optimize speed))

(defstruct (dense-matrix-mod-p
	    ;; Constructors: make-[...], (easier) make-[...]-zero
	    (:copier nil)
	    (:predicate nil)) ;; dense-matrix-mod-p-p returns the prime p
  "The class of m-by-n arrays of integers modulo a prime p of Z.
The data is stored in the vector 'mat' of length m*n in row-major order."
  mat m n p)

(defun make-dense-matrix-mod-p-zero (m n p)
  "Returns an m-by-n matrix mod p, initialized with 0's."
  (assert (typep m 'nnfixnum) (m)
    "The row dimension ~D should be a non-negative fixnum." m)
  (assert (typep n 'nnfixnum) (n)
    "The column dimension ~D should be a non-negative fixnum." n)
  (assert (primep p) (p) "p = ~D is not a prime." p)
  (make-dense-matrix-mod-p
   :mat (make-array (* m n) :initial-element 0) :m m :n n :p (abs p)))

(defmacro with-dense-matrix-mod-p-slots (slots var &body body)
  "Version of with-slots for dense-matrix-mod-p, with type declarations.
Does not support setf."
  (if (endp slots)
      `(progn ,@body)
    (if (atom (first slots))
        `(with-dense-matrix-mod-p-slots
             ,(cons (list (first slots) (first slots)) (rest slots))
           ,var ,@body)
      (let ((var-name (first (first slots)))
            (slot-name (second (first slots)))
            accessor type)
        (ecase slot-name
          (mat (setq accessor 'dense-matrix-mod-p-mat type 'vector))
	  (m (setq accessor 'dense-matrix-mod-p-m type 'nnfixnum))
	  (n (setq accessor 'dense-matrix-mod-p-n type 'nnfixnum))
          (p (setq accessor 'dense-matrix-mod-p-p type '(integer 2 *))))
        `(let ((,var-name (,accessor (the dense-matrix-mod-p ,var))))
           (declare (type ,type ,var-name))
           (with-dense-matrix-mod-p-slots ,(rest slots) ,var ,@body))))))

(defmethod m-num-rows ((aa dense-matrix-mod-p))
  (dense-matrix-mod-p-m aa))

(defmethod m-num-cols ((aa dense-matrix-mod-p))
  (dense-matrix-mod-p-n aa))

(defmethod mat ((aa dense-matrix-mod-p))
  "Returns the underlying vector of integers.  It is of length m*n,
with the data stored in row-major order."
  (dense-matrix-mod-p-mat aa))

(defun row-reduce-mod-p (aa)
  "Input: a dense-matrix-mod-p aa.  The function does row operations
destructively, by Gaussian elimination, to put aa into row-echelon form.
  Returns a sorted list L of the columns that have pivots.  The pivots
are located at [i,j] = [0, (elt L 0)], [1, (elt L 1)], etc."
  (with-dense-matrix-mod-p-slots ((a mat) m n p) aa
    (macrolet ((ind (i j) `(the nnfixnum (+ (the nnfixnum (* n ,i)) ,j)))
	       (aaref (k) `(the integer (svref a ,k))))
      (let ((i0 0)
	    (i1 0)
	    (j0 0)
	    (ind-i1-j0 0)
	    (piv-cols '()))
	(declare (type nnfixnum i0 i1 j0 ind-i1-j0) (list piv-cols))
	(loop
	  (cond ((or (= i0 m) (= j0 n))
		 (return-from row-reduce-mod-p (nreverse piv-cols)))
		((= i1 m)
		 (incf j0)
		 (setq i1 i0
		       ind-i1-j0 (ind i1 j0)))
		((zerop (the integer (rem (aaref ind-i1-j0) p)))
		 (incf i1)
		 (incf ind-i1-j0 n))
		(t ;; New pivot is at i1,j0.
		 ;; Swap rows so pivot goes to row i0.
		 (unless (= i0 i1)
		   (do ((j j0 (1+ j))
			(ind-i0-j (ind i0 j0) (1+ ind-i0-j))
			(ind-i1-j ind-i1-j0 (1+ ind-i1-j)))
		       ((= j n))
		     (declare (type nnfixnum j ind-i0-j ind-i1-j))
		     (psetf (svref a ind-i0-j) (svref a ind-i1-j)
			    (svref a ind-i1-j) (svref a ind-i0-j))))
		 ;; Divide through row i0 to make pivot 1.
		 (let ((ind-i0-j0 (ind i0 j0)))
		   (declare (type nnfixnum ind-i0-j0))
		   (let ((piv-old (aaref ind-i0-j0)))
		     (declare (integer piv-old))
		     (unless (= (mod piv-old p) 1) ;; 1 or 1-p
		       (let ((piv-inv (inv-mod piv-old p)))
			 (declare (integer piv-inv))
			 (do ((j (1+ j0) (1+ j))
			      (ind-i0-j (1+ ind-i0-j0) (1+ ind-i0-j)))
			     ((= j n))
			   (declare (type nnfixnum j ind-i0-j))
			   (setf (svref a ind-i0-j)
			     (rem (the integer (* (aaref ind-i0-j) piv-inv))
				  p)))))
		     (setf (svref a ind-i0-j0) 1))
		   ;; Subtract multiples of row i0 from the other rows, both
		   ;; above and below, to clear out the pivot column.
		   (do ((i 0 (1+ i))
			(ind-i-j0 j0 (+ ind-i-j0 n)))
		       ((= i m))
		     (declare (type nnfixnum i ind-i-j0))
		     (unless (= i i0)
		       (let ((old (rem (aaref ind-i-j0) p)))
			 (declare (integer old))
			 (setf (svref a ind-i-j0) 0)
			 (unless (zerop old)
			   (do ((j (1+ j0) (1+ j))
				(ind-i0-j (1+ ind-i0-j0) (1+ ind-i0-j))
				(ind-i-j (1+ ind-i-j0) (1+ ind-i-j)))
			       ((= j n))
			     (declare (type nnfixnum j ind-i0-j ind-i-j))
			     (setf (svref a ind-i-j)
			       (rem (the integer
				      (- (aaref ind-i-j)
					 (the integer (* old (aaref ind-i0-j)))))
				    p))))))))
		 (push j0 piv-cols)
		 (incf i0)
		 (incf j0)		       
		 (setq i1 i0
		       ind-i1-j0 (ind i1 j0)))))))))
	    
(defmethod m-ker ((aa dense-matrix-mod-p) &optional make-sp)
  "Returns a dense-matrix-mod-p whose columns are a basis of
the kernel of a.  The input aa is destroyed along
the way; at the end, it contains aa in row-echelon form, the result
of row-reduce-mod-p.  make-sp is ignored."
  (declare (ignore make-sp))
  (with-dense-matrix-mod-p-slots ((a mat) n p) aa
    (macrolet ((aaref (i j) `(the integer (svref a (the nnfixnum (+ (the nnfixnum (* n ,i)) ,j))))))
      (let ((piv-cols (row-reduce-mod-p aa))) ;; overwrites a
	(declare (list piv-cols))
	(let* ((kerdim (- n (length piv-cols)))
	       (bb (make-dense-matrix-mod-p-zero n kerdim p))
	       (j-list piv-cols) ;; poppable copy; piv-cols will be unchanged
	       (j 0)
	       (k 0))
	  (declare (type nnfixnum kerdim j k) (list j-list))
	  (with-dense-matrix-mod-p-slots ((b mat)) bb
	    (macrolet ((bbref (i j) `(the integer (svref b (the nnfixnum (+ (the nnfixnum (* kerdim ,i)) ,j))))))
	      (loop
		(cond ((= j n)
		       (assert (= k kerdim) () "Counting error with k.")
		       (return-from m-ker bb))
		      ((and (not (endp j-list))
			    (= j (the nnfixnum (first j-list))))
		       (pop j-list)
		       (incf j))
		      (t
		       (setf (bbref j k) 1)
		       (do ((i 0 (1+ i))
			    (piv-j-list piv-cols (rest piv-j-list)))
			   ((endp piv-j-list))
			 (declare (type nnfixnum i))
			 (setf (bbref (the nnfixnum (first piv-j-list)) k)
			   (rem (the integer (- (aaref i j))) p)))
		       (incf j)
		       (incf k)))))))))))   

;;; -------------------- Unit tests --------------------

(dolist (p '(2 5))
  (dotimes (a p)
    (dotimes (b p)
      (dotimes (c p)
	(dotimes (d p)
	  (let ((aa (make-dense-matrix-mod-p-zero 2 2 p))
		(rank (if (and (= a 0) (= b 0) (= c 0) (= d 0))
			  0
			(if (= (rem (- (* a d) (* b c)) p) 0)
			    1
			  2))))
	    (setf (svref (mat aa) 0) a
		  (svref (mat aa) 1) b
		  (svref (mat aa) 2) c
		  (svref (mat aa) 3) d)
	    (let ((piv (row-reduce-mod-p aa)))
	      (labels ((aver (test)
			 (assert test ()
			   "Error: turned~&~D ~D~&~D ~D~&into~&~D ~D~&~D ~D~&with piv ~S~&"
			   a b
			   c d
			   (svref (mat aa) 0) (svref (mat aa) 1)
			   (svref (mat aa) 2) (svref (mat aa) 3)
			   piv)))
		(ecase rank
		  (0
		   (aver (endp piv))
		   (aver (= (svref (mat aa) 0) 0))
		   (aver (= (svref (mat aa) 1) 0))
		   (aver (= (svref (mat aa) 2) 0))
		   (aver (= (svref (mat aa) 3) 0)))
		  (1
		   (aver (equalp piv (if (and (= a 0) (= c 0)) '(1) '(0))))
		   (aver (or (and (equalp piv '(0))
				  (= (svref (mat aa) 0) 1))
			     (and (equalp piv '(1))
				  (= (svref (mat aa) 0) 0)
				  (= (svref (mat aa) 1) 1))))
		   (aver (= (svref (mat aa) 2) 0))
		   (aver (= (svref (mat aa) 3) 0)))
		  (2
		   (aver (equalp piv '(0 1)))
		   (aver (= (svref (mat aa) 0) 1))
		   (aver (= (svref (mat aa) 1) 0))
		   (aver (= (svref (mat aa) 2) 0))
		   (aver (= (svref (mat aa) 3) 1))))))))))))

(dolist (p '(2 5 12379 31991))
  (with-open-file (si "test11.lisp" :direction :input)
    (let ((m (read si))
	  (n (read si)))
      (let ((aa (make-dense-matrix-mod-p-zero m n p)))
	(loop
	  (let ((i (read si nil)))
	    (unless i
	      (return))
	    (let ((j (read si))
		  (v (read si)))
	      (setf (svref (mat aa) (+ (* n i) j)) (rem v p)))))
	(let ((rank (length (row-reduce-mod-p aa)))
	      (expected-rank (if (zerop (rem 10 p)) 139 140)))
	  (assert (= rank expected-rank) ()
	    "Expected rank ~D, got ~D, modulo ~D." expected-rank rank p))))))
