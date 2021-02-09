(in-package shh2)

(declaim (optimize speed))

;;; Operations are valid over any commutative ring with identity,
;;; except for a few where we note that we've assumed a domain.  Those
;;; few are noted in the documentation.

(deftype sparse-v ()
  "A sparse-v is a proper list of sparse-elts representing a vector
over the integral domain D.  The i-th entry in the vector is the value
of the sparse-elt whose index is i.  If no sparse-elt has index i,
it means the i-th entry in the vector has value 0; indeed, to say the
vector is sparse is to say there is no sparse-elt for most i.  The
sparse-elts must have distinct non-negative indices and be sorted in
order of increasing index.  A sparse-elt with zero value must never
appear in a sparse-v.
  A sparse-v must never share top-level list structure with another
list, because we often destructively modify the top-level structure,
as in with-splicer.
  Two sparse-v's are mathematically equal iff they are equalp.
  When a function's documentation mentions the 'census', the function
returns two values, the result, which is a sparse-v, and the census.
The census says which sparse-elts were born [changed from zero to
non-zero] or died [changed from non-zero to zero].  It is a list of
fixnums i1, where i1 >= 0 means a birth at index i = i1, and i1 <= -1
means a death at index i = -1-i1.  The census is ordered by increasing
i."
  'list)

(defun input-sparse-v (val-list &optional (make-sp #'make-sp-z))
  "Converts a dense list of values to a sparse-v.  The optional
argument make-sp is a function of two arguments, i and v,
where the v's come from val-list.  make-sp should construct
an appropriate sparse-elt from i and v.  make-sp defaults to
the constructor over the ring of integers Z.
Example: (input-sparse-v '(17 0 19)) has value 17 at index 0
and 19 at index 2.  The 17 and 19 in the result belong to Z."
  (do ((i 0 (1+ i))
       (tail val-list (rest tail))
       (ans '() (let ((e (funcall make-sp i (first tail))))
		  (if (sp-zerop e) ans (cons e ans)))))
      ((endp tail) (nreverse ans))
    (declare (type sparse-v ans))))

(defun v-print-line-by-line (stream a n &optional (zero-str "0"))
  "Prints the sparse-v a to the stream, densely (with 0's included),
and with each entry at the start of a fresh line.  The dimension
is n; we print entries with indices 0, ..., n-1.  The argument
zero-str is the print value of the zero element of D; it defaults
to the string 0."
  (declare (type sparse-v a))
  (dotimes-f (i n)
    (format stream "~&")
    (if (or (endp a) (< i (sp-i (first a))))
	(format stream zero-str)
      (sp-print-value (pop a) stream))))

(defun v-add (a b)
  "Given sparse-v's a and b, destructively alters a to hold their sum.
Returns the altered a and the census.  Does not alter b."
  (declare (type sparse-v a b))
  (let ((census '()))
    (declare (list census))
    (with-splicer a
      (till (or (splicer-endp) (endp b))
	(let ((ae (splicer-read)))
	  (let ((ai (sp-i ae))
		(bi (sp-i (first b))))
	    (declare (type nnfixnum ai bi))
	    (cond ((< ai bi)
		   (splicer-fwd))
		  ((> ai bi)
		   (splicer-insert (pop b))
		   (push bi census)
		   (splicer-fwd))
		  (t
		   (let ((ce (sp-add ae (pop b))))
		     (cond ((sp-zerop ce)
			    (splicer-delete)
			    (push (- -1 bi) census))
			   (t
			    (splicer-modify ce)
			    (splicer-fwd)))))))))
      (when (splicer-endp)
	(dolist (be b)
	  (splicer-nconc (list be))
	  (splicer-fwd)
	  (push (sp-i be) census)))
      (values a (nreverse census)))))

(define-modify-macro v-add-f (&rest args) v-add
  "Same as v-add, but sets the altered argument to the result.")
    
(defun v-add-nondestr (a b)
  "Returns the sum of the sparse-v's a and b, but, unlike v-add, alters
neither a nor b."
  (declare (type sparse-v a b))
  (let ((ans '()))
    (declare (type sparse-v ans))
    (till (or (endp a) (endp b))
      (let ((ai (sp-i (first a)))
            (bi (sp-i (first b))))
        (declare (type nnfixnum ai bi))
        (cond ((< ai bi) (push (pop a) ans))
              ((> ai bi) (push (pop b) ans))
              (t
               (let ((ce (sp-add (pop a) (pop b))))
                 (unless (sp-zerop ce)
                   (push ce ans)))))))
    (nreconc ans (copy-list (if (endp a) b a)))))

(defun v-subtract (a b)
  "Given sparse-v's a and b, destructively alters a to hold their
difference.  Returns the altered a and the census.  Does not alter b."
  (declare (type sparse-v a b))
  (let ((census '()))
    (declare (list census))
    (with-splicer a
      (till (or (splicer-endp) (endp b))
	(let ((ae (splicer-read)))
	  (let ((ai (sp-i ae))
		(bi (sp-i (first b))))
	    (declare (type nnfixnum ai bi))
	    (cond ((< ai bi)
		   (splicer-fwd))
		  ((> ai bi)
		   (splicer-insert (sp-negate (pop b)))
		   (push bi census)
		   (splicer-fwd))
		  (t
		   (let ((ce (sp-subtract ae (pop b))))
		     (cond ((sp-zerop ce)
			    (splicer-delete)
			    (push (- -1 bi) census))
			   (t
			    (splicer-modify ce)
			    (splicer-fwd)))))))))
      (when (splicer-endp)
	(dolist (be b)
	  (splicer-nconc (list (sp-negate be)))
	  (splicer-fwd)
	  (push (sp-i be) census)))
      (values a (nreverse census)))))

(defun v-subtract-nondestr (a b)
  "Returns the difference of the sparse-v's a and b, altering
neither a nor b."
  (declare (type sparse-v a b))
  (let ((ans '()))
    (declare (type sparse-v ans))
    (till (or (endp a) (endp b))
      (let ((ai (sp-i (first a)))
            (bi (sp-i (first b))))
        (declare (type nnfixnum ai bi))
        (cond ((< ai bi) (push (pop a) ans))
              ((> ai bi) (push (sp-negate (pop b)) ans))
              (t
               (let ((ce (sp-subtract (pop a) (pop b))))
                 (unless (sp-zerop ce)
                   (push ce ans)))))))
    (if (endp a)
	(dolist (e b (nreverse ans))
	  (push (sp-negate e) ans))
      (nreconc ans (copy-list a)))))

(defun v-scalar-mult (a fac)
  "Destructively alters the sparse-v a to hold its scalar multiple by
the value in the sparse-elt fac.  Returns the altered a.  Here
we use the fact that D is a domain, because we take for granted that
the product of two non-zero values is non-zero."
  (declare (type sparse-v a))
  (cond ((sp-onep fac)
         a)
        ((sp-neg-one-p fac)
         (v-negate a))
        ((sp-zerop fac)
         '())
        (t
         (do ((tail a (rest tail)))
             ((endp tail) a)
           (declare (type sparse-v tail))
           (rplaca tail (sp-mult (first tail) fac))))))

(define-modify-macro v-scalar-mult-f (&rest args) v-scalar-mult
  "Same as v-scalar-mult, but sets the sparse-v argument to the result.")
    
(defun v-negate (a)
  "Destructively alters the sparse-v a to hold its scalar multiple
by -1.  Returns the altered a."
  (declare (type sparse-v a))
  (do ((tail a (rest tail)))
      ((endp tail) a)
    (declare (type sparse-v tail))
    (rplaca tail (sp-negate (first tail)))))

(define-modify-macro v-negate-f (&rest args) v-negate
  "Same as v-negate, but sets the argument to the result.")
    
(defun v-negate-nondestr (a)
  "Returns the scalar multiple of a by -1.  Does not alter a."
  (declare (type sparse-v a))
  (mapcar #'(lambda (e) (sp-negate e)) a))
    
(defun v-alter (a fac b)
  "Given sparse-v's a and b, destructively alters a to hold a + c * b,
where c is the value in fac.  Returns the altered a and the census.
Does not alter b.  Assumes D is an integral domain, so that the product
of non-zero values is non-zero."
  (declare (type sparse-v a b))
  (cond ((sp-onep fac)
         (v-add a b))
	((sp-neg-one-p fac)
	 (v-subtract a b))
        ((sp-zerop fac)
         (values a '()))
        (t 
	 (let ((census '()))
	   (declare (list census))
	   (with-splicer a
	     (till (or (splicer-endp) (endp b))
	       (let ((ae (splicer-read)))
		 (let ((ai (sp-i ae))
		       (bi (sp-i (first b))))
		   (declare (type nnfixnum ai bi))
		   (cond ((< ai bi)
			  (splicer-fwd))
			 ((> ai bi)
			  (splicer-insert (sp-mult fac (pop b) bi))
			  (push bi census)
			  (splicer-fwd))
			 (t
			  (let ((ce (sp-add ae
					    (sp-mult fac (pop b) bi))))
			    (cond ((sp-zerop ce)
				   (push (- -1 bi) census)
				   (splicer-delete))
				  (t
				   (splicer-modify ce)
				   (splicer-fwd)))))))))
	     (when (splicer-endp)
	       (dolist (be b)
		 (splicer-nconc (list (sp-mult be fac)))
		 (splicer-fwd)
		 (push (sp-i be) census)))
	     (values a (nreverse census)))))))

(define-modify-macro v-alter-f (&rest args) v-alter
  "Same as v-alter, but sets the first sparse-v argument to the result.")
    
(defun v-alter-elt (a i1 fac i2)
  "Alters the i1-th entry of a by adding to it [value of fac] times
[value of the i2-th entry of a].  Returns the altered a and the census."
  (declare (type sparse-v a) (type nnfixnum i1 i2))
  (let ((census '()))
    (declare (list census))
    (block no-change
      (when (sp-zerop fac)
	(return-from no-change))
      (let ((e2 nil))
	(with-splicer a
	  ;; The till loop has two goals: (.) bind e2 to the i2-th entry
	  ;; if we get to it before i1, and (.) stop the splicer at the
	  ;; i1-th entry or its insertion point if it doesn't exist.
	  (till (splicer-endp)
	    (let ((i (sp-i (splicer-read))))
	      (declare (type nnfixnum i))
	      (unless e2
		(if (> i i2)
		    (return-from no-change)
		  (when (= i i2)
		    (setq e2 (splicer-read)))))
	      (if (>= i i1)
		  (return) ;; from the till
		(splicer-fwd))))
	  ;; If you haven't found e2 yet, keep looking.
	  (unless e2
	    (dolist (ae (splicer-tail))
	      (let ((i (sp-i ae)))
		(declare (type nnfixnum i))
		(if (> i i2)
		    (return-from no-change)
		  (when (= i i2)
		    (setq e2 ae)
		    (return)))))) ;; from the dolist
	  (when e2
	    (let ((e (sp-mult fac e2 i1))
		  (has-i1 (and (not (splicer-endp))
			       (= i1 (sp-i (splicer-read))))))
	      (when has-i1
		(setq e (sp-add (splicer-read) e)))
	      (if (sp-zerop e)
		  (when has-i1
		    (splicer-delete)
		    (push (- -1 i1) census))
		(if has-i1
		    (splicer-modify e)
		  (progn
		    (splicer-insert e)
		    (push i1 census)))))))))
      (values a (nreverse census))))

(defun v-negate-elt (a i)
  "Negates the i-th element of the sparse-v a.  Returns the altered a."
  (declare (type sparse-v a) (type nnfixnum i))
  (do ((tail a (rest tail)))
      ((endp tail) a)
    (declare (type sparse-v tail))
    (let* ((e0 (first tail))
	   (i0 (sp-i e0)))
      (declare (type nnfixnum i0))
      (when (>= i0 i)
        (when (= i0 i)
          (rplaca tail (sp-negate e0)))
        (return a)))))

(define-modify-macro v-negate-elt-f (&rest args) v-negate-elt
  "Same as v-negate-elt, but sets the sparse-v argument to the result.")
    
(defun v-swap (a i1 i2)
  "Destructively alters the sparse-v a by swapping the i1-th and
i2-th entries.  Returns the altered a."
  ;; Census code is complete but commented out.
  (declare (type sparse-v a) (type nnfixnum i1 i2))
  (if (= i1 i2)
      (values a '())
    (if (> i1 i2)
        (v-swap a i2 i1)
      (let ((left '())
            (left-last '())
            (at1 nil)
            (middle-plus '())
            (middle '())
            (middle-last '())
            (at2 nil)
            (right '())
	    #|(census '())|#)
        (declare (type sparse-v left left-last middle-plus
                       middle middle-last right)
		 #|(list census)|#)
        (with-splicer a
          (till (or (splicer-endp) (>= (sp-i (splicer-read)) i1))
            (splicer-fwd))
          (multiple-value-bind (ll ll-last mm) (splicer-split)
            (declare (type sparse-v ll ll-last mm))
            (setq left ll
                  left-last ll-last)
            (if (or (endp mm) (> (sp-i (first mm)) i1))
                (setq middle-plus mm)
              (setq at1 (first mm)
                    middle-plus (rest mm)))))
        (with-splicer middle-plus
          (till (or (splicer-endp) (>= (sp-i (splicer-read)) i2))
            (splicer-fwd))
          (multiple-value-bind (ll ll-last mm) (splicer-split)
            (declare (type sparse-v ll ll-last mm))
            (setq middle ll
                  middle-last ll-last)
            (if (or (endp mm) (> (sp-i (first mm)) i2))
                (setq right mm)
              (setq at2 (first mm)
                    right (rest mm)))))
        (let ((ans right))
          (declare (type sparse-v ans))
          (when at1
            (push (copy-sp at1 i2) ans))
          (when middle
            (rplacd middle-last ans)
            (setq ans middle))
          (when at2
            (push (copy-sp at2 i1) ans))
          (when left
            (rplacd left-last ans)
            (setq ans left))
	  #|
	  (if (and at1 (not at2))
	  (setq census (list (- -1 i1) i2))
	  (when (and at2 (not at1))
	  (setq census (list i1 (- -1 i2)))))
	  (values ans census) ;; if you want the census
	  |#
          ans))))) ;; if you don't want the census

(define-modify-macro v-swap-f (&rest args) v-swap
  "Same as v-swap, but sets the altered argument to the result.")
    
(defun v-dot (a b)
  "Returns a sparse-elt whose value is the dot product of a and b.
If the dot product is zero, returns either nil or a sparse-elt
of value zero."
  (declare (type sparse-v a b))
  (let ((ans nil))
    (till (or (endp a) (endp b))
      (let ((ai (sp-i (first a)))
            (bi (sp-i (first b))))
        (declare (type nnfixnum ai bi))
        (cond ((< ai bi) (pop a))
              ((> ai bi) (pop b))
              (t 
	       (let ((prod (sp-mult (pop a) (pop b))))
		 (setq ans (if ans (sp-add ans prod) prod)))))))
    ans))

(defun v-get (a i)
  "Returns the sparse-elt of index i in the sparse-v a, or nil if
the value is zero there."
  (declare (type sparse-v a) (fixnum i))
  (dolist (ae a nil)
    (let ((i0 (sp-i ae)))
      (declare (type nnfixnum i0))
      (when (>= i0 i)
	(return (if (= i0 i) ae nil))))))

(defun v-set (a i new-elt)
  "Destructively alters the sparse-v a so the i-th elt has the
value of new-elt.  Returns the altered a and the census."
  (declare (type sparse-v a) (type nnfixnum i))
  (with-splicer a
    (let ((has-i nil))
      (till (splicer-endp)
	(cond ((>= (sp-i (splicer-read)) i)
	       (setq has-i (= (sp-i (splicer-read)) i))
	       (return)) ;; from 'till'
	      (t
	       (splicer-fwd))))
      (let ((new-is-zero (or (null new-elt) (sp-zerop new-elt)))
	    (census '()))
	(declare (list census))
	(if has-i
	    (cond (new-is-zero
		   (splicer-delete)
		   (push (- -1 i) census))
		  (t
		   (splicer-modify (copy-sp new-elt i))))
	  (unless new-is-zero
	    (splicer-insert (copy-sp new-elt i))
	    (push i census)))
	(values a census)))))

(defun v-zerop (a)
  "Whether the sparse-v a is the zero vector."
  (declare (type sparse-v a))
  (endp a))

(defun v-singleton-p (a)
  "Whether the sparse-v a has exactly one non-zero element."
  (declare (type sparse-v a))
  (and (not (endp a)) (endp (rest a))))

(defgeneric integrity-check (A &key message &allow-other-keys)
  (:documentation
   "Signals an error if A has internal errors.  Otherwise does nothing
and returns nil.  The optional keyword argument 'message' will be
prepended to the error messages; it should include any formatting
like ': ' that's desired at the end.  Individual methods may define
other keys."))

(defmethod integrity-check ((A list) &key (message "") m)
  "The list A is assumed to be a sparse-v.  The optional key :m gives
the dimension of the vector space containing A."
  (when A
    (let ((ae (first A)))
      (assert (not (sp-zerop ae)) ()
	"~Asparse-v has a zero entry: ~A" message ae)
      (assert (>= (sp-i ae) 0) ()
	"~Asparse-v index ~D should be >= 0." message (sp-i ae))
      (sp-integrity-check ae :message message)
      (if (endp (rest A))
	  (when m
	    (assert (< (sp-i ae) m) ()
	      "~Asparse-v index ~D should be < dim ~D."
	      message (sp-i ae) m))
	(assert (< (sp-i ae) (sp-i (second A))) ()
	  "~AUnsorted sparse-v: index ~D not < ~D."
	  message (sp-i ae) (sp-i (second A))))
      (integrity-check (rest A) :message message :m m))))

;;; -------------------- Unit tests over Z --------------------

(block unit-tests-over-z
  (handler-bind ((error #'(lambda (condition)
			    (declare (ignore condition))
			    (return-from unit-tests-over-z))))
    ;; If make-sp-z itself throws an error, it means Z is unavailable.
    (make-sp-z 12379 31991))
  (labels ((vl (lyst) (input-sparse-v lyst))
	   (cen (la lc)
	     (do ((ta la (rest ta))
		  (tc lc (rest tc))
		  (i 0 (1+ i))
		  (ans '() (if (and (zerop (first ta))
				    (not (zerop (first tc))))
			       (cons i ans)
			     (if (and (not (zerop (first ta)))
				      (zerop (first tc)))
				 (cons (- -1 i) ans)
			       ans))))
		 ((endp ta) (nreverse ans)))))
    (labels ((add-subtr-test (l1 l2)
	       (multiple-value-bind (ans census) (v-add (vl l1) (vl l2))
		 (assert (equalp ans (vl (mapcar #'+ l1 l2))))
		 (assert (equal census (cen l1 (mapcar #'+ l1 l2)))))
	       (multiple-value-bind (ans census) (v-subtract (vl l1) (vl l2))
		 (assert (equalp ans (vl (mapcar #'- l1 l2))))
		 (assert (equal census (cen l1 (mapcar #'- l1 l2)))))
	       (assert (equalp (v-add-nondestr (vl l1) (vl l2))
			       (vl (mapcar #'+ l1 l2))))
	       (assert (equalp (v-subtract-nondestr (vl l1) (vl l2))
			       (vl (mapcar #'- l1 l2))))))
      (add-subtr-test '(5 0 7 0) '(0 6 0 8))
      (add-subtr-test '(0 6 0 8) '(5 0 7 0))
      (add-subtr-test '(10 20 30) '(40 50 60))
      (add-subtr-test '(40 50 60) '(10 20 30))
      (add-subtr-test '(10 20 30) '(40 -20 60))
      (add-subtr-test '(40 -20 60) '(10 20 30))
      (dotimes (a 3)
	(dotimes (b 3)
	  (dotimes (c 3)
	    (dotimes (d 3)
	      (dotimes (e 3)
		(dotimes (f 3)
		  (add-subtr-test (list (1- a) (1- b) (1- c))
				  (list (1- d) (1- e) (1- f))))))))))
    (labels ((scmult-test (l1 c)
	       (assert (equalp (v-scalar-mult (vl l1) (make-sp-z -1 c))
			       (vl (mapcar #'(lambda (v) (* c v)) l1)))))
	     (negate-test (l1)
	       (assert (equalp (v-negate (vl l1))
			       (vl (mapcar #'- l1))))
	       (assert (equalp (v-negate-nondestr (vl l1))
			       (vl (mapcar #'- l1)))))
	     (alter-test (l1 c l2)
	       (multiple-value-bind (ans census) (v-alter (vl l1) (make-sp-z -1 c) (vl l2))
		 (assert (equalp ans (vl (mapcar #'(lambda (x1 x2)
						     (+ x1 (* c x2)))
						 l1 l2))))
		 (assert (equal census (cen l1 (mapcar #'(lambda (x1 x2)
							   (+ x1 (* c x2)))
						       l1 l2))))))
	     (dot-test (l1 l2)
	       (let ((dot (v-dot (vl l1) (vl l2))))
		 (assert (= (if dot (sp-integer-value dot) 0)
			    (apply #'+ (mapcar #'* l1 l2)))))))
      (dotimes (a1 3)
	(dotimes (a2 3)
	  (dotimes (a3 3)
	    (negate-test (list (1- a1) (1- a2) (1- a3)))
	    (dotimes (c 3)
	      (scmult-test (list (1- a1) (1- a2) (1- a3)) c)
	      (dotimes (b1 3)
		(dotimes (b2 3)
		  (dotimes (b3 3)
		    (alter-test (list (1- a1) (1- a2) (1- a3))
				(1+ c)
				(list (1- b1) (1- b2) (1- b3)))
		    (when (zerop c)
		      (dot-test (list (1- a1) (1- a2) (1- a3))
				(list (1- b1) (1- b2) (1- b3))))))))))))
    (labels ((alter-elt-test (l i1 c i2)
	       (let ((ans-l (copy-list l)))
		 (setf (elt ans-l i1) (+ (elt ans-l i1) (* c (elt ans-l i2))))
		 (multiple-value-bind (ans census) (v-alter-elt (vl l) i1 (make-sp-z -1 c) i2)
		   (assert (equal (vl ans-l) ans))
		   (assert (equal (cen l ans-l) census)))))
	     (negate-elt-test (l i)
	       (assert (equal (v-negate-elt (vl l) i)
			      (vl (mapcar #'(lambda (k0 k1)
					      (if (= k1 i) (- k0) k0))
					  l '(0 1 2))))))
	     (get-test (l i)
	       (assert (equal (v-get (vl l) i)
			      (if (zerop (elt l i))
				  nil
				(make-sp-z i (elt l i))))))
	     (set-test (l i c)
	       (let ((ans-l (mapcar #'(lambda (old-val ii)
					(if (= ii i) c old-val))
				    l '(0 1 2))))
		 (multiple-value-bind (ans census) (v-set (vl l) i (make-sp-z -1 c))
		   (assert (equal (vl ans-l) ans))
		   (assert (equal (cen l ans-l) census))))))
      (dotimes (a1 3)
	(dotimes (a2 3)
	  (dotimes (a3 3)
	    (dotimes (i1 3)
	      (negate-elt-test (list (1- a1) (1- a2) (1- a3)) i1)
	      (get-test (list (1- a1) (1- a2) (1- a3)) i1)
	      (dotimes (c 2)
		(set-test (list (1- a1) (1- a2) (1- a3)) i1 c)
		(dotimes (i2 3)
		  (alter-elt-test (list (1- a1) (1- a2) (1- a3))
				  i1 (1+ c) i2))))))))
    (labels ((swap-test (l i1 i2)
	       (assert (equal (v-swap (vl l) i1 i2)
			      (vl (mapcar #'(lambda (k)
					      (if (= k i1)
						  (elt l i2)
						(if (= k i2)
						    (elt l i1)
						  (elt l k))))
					  '(0 1 2 3 4)))))))
      (dotimes (a1 3)
	(dotimes (a2 3)
	  (dotimes (a3 3)
	    (dotimes (a4 3)
	      (dotimes (a5 3)
		(dotimes (i1 5)
		  (dotimes (i2 5)
		    (swap-test (list (1- a1) (1- a2) (1- a3) (1- a4) (1- a5))
			       i1 i2)))))))))))
