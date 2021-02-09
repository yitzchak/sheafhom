(in-package shh2)

;;; ------------------------- Contract for mset -------------------------

(defclass mset (cat-obj)
  ()
  (:documentation
"An mset is a set in the mathematical sense, either finite or
infinite.  An mset S must obey the contract [1]-[5].
  [1] (mset-member elt S) returns true if and only if elt is an element
of S.
  [2] (mset-size S) returns the number of elements in S, as an integer,
when the number is finite and known.  If S is infinite or of unknown
size, the method returns nil.
  [3] (mset-iterator S) returns an iterator for S.  In this code, an
iterator is a function f of no arguments, such that repeated calls to
f return the elements of S one at a time, and f returns nil when the
iteration is done.  The implementation must guarantee the iterator
produces each element once and only once.  ('Only once' is the main
property distinguishing sets from more general kinds of collections.)
The elements can appear in any order, although some iterators will
always use a certain order and will document this fact.
  [4] nil must not be an element of an mset.  (This allow an iterator to
return nil to signal it's finished.)
  [5] msets are immutable.  You can't add or delete elements once the
set is created.
  Most mset methods are defined in terms of [1]-[3].  For example,
do-mset is the preferred way to iterate over a set.
  When an mset is infinite, methods that involve looking at more than
one element may run forever, so use caution.  Some methods avoid this
risk by doing nothing when (mset-size S) is nil.  For instance,
mset-equal can't determine if two sets are equal if it can't tell how
big they are.
  See hash-set for a implementation based on a hash-table, useful for
small to medium sets.  make-hash-set creates a hash-set from different
kinds of inputs.  Lazy-set is a framework for defining an mset by
hand, useful especially for large sets and with lazy evaluation.  A
notable example is *primes* in numthy.lisp.
  A future version of Sheafhom may remove mset entirely and replace it
with 'series', a de-facto standard Common Lisp package supporting
iterators and lazy evaluation."))

(defgeneric mset-member (elt set)
  (:documentation "See mset."))

(defgeneric mset-size (set)
  (:documentation "See mset."))

(defgeneric mset-iterator (set)
  (:documentation "See mset."))

(defmacro do-mset ((var set &optional result) &body body)
  "Executes body once for each element of the mset set, with var bound
to the element, and then returns result."
  (let ((iter (gensym)))
    `(let ((,iter (mset-iterator ,set)))
       (do ((,var (funcall ,iter) (funcall ,iter)))
	   ((null ,var) ,result)
	 ,@body))))

;;; ------------------------- Lazy-set -------------------------

(defclass lazy-set (mset)
  ((iterator-factory :initarg :iterator-factory :type function
		     :documentation
"An iterator-factory is a function of no arguments.  Each call to this
function returns a new iterator for this mset.  See [3] in the
documentation for mset.")
   (containment-test :initarg :containment-test :type function
		     :documentation
"Holds a function of one argument 'elt' that returns true if and only
if elt is an element of this mset.  The test should be fast.  The
preferred way to do containment tests is with mset-member.")
   (size :initarg :size :initform nil :type (or (integer 0 *) null)
   :documentation
"The number of elements in the set, or nil if the number is infinite
or unknown."))
  (:documentation "A framework for defining an mset by hand."))

(defmethod mset-iterator ((set lazy-set))
  (funcall (slot-value set 'iterator-factory)))

(defmethod mset-member (elt (set lazy-set))
  (funcall (slot-value set 'containment-test) elt))

(defmethod mset-size ((set lazy-set))
  (slot-value set 'size))

;;; ------------------------- Hash-set -------------------------

(defclass hash-set (mset)
  ((table :reader table :initarg :table :type hash-table))
  (:documentation
"An implementation of mset backed by an equalp hash-table.  The
elements elt of the set are the table's values, and the key for elt
is (equalp-key elt).  See equalp-key."))

(defgeneric equalp-key (elt)
  (:documentation
"Elements elt1 and elt2 of a hash-set are considered 'equal' in an
mset S if and only if (equalp (equalp-key elt1) (equalp-key elt2))
holds.  In other words, equalp-key must map equal elements of S to the
same key, and must be injective on non-equal elements of S.
  It is always hard to handle conflicting notions of equality in a
computer language.  In Java, one notion of equality is 'equals', a
function users can extend any way they like.  To make Java's
Hashtables handle 'equals' properly, users have an extra
responsibility: to extend the function hashCode to guarantee that
objects that are the same under 'equals' will have the same hashCode.
In Lisp, hash-tables use built-in equality tests and hash-code
algorithms, neither of which the user can extend.  Sheafhom provides
equalp-key as a workaround: it ensures that elements that are equal
in S will appear equal in a hash-table."))

(defmethod equalp-key ((elt t))
  "If an mset S uses this default implementation, elements of S are
equal in S if and only if they are equal under Lisp's 'equalp'."
  elt)

(defmacro put-with-equalp-key (value table)
  "Puts value into the given hash-table using (equalp-key value) as the key."
  (let ((v (gensym)))
    `(let ((,v ,value))
       (puthash (equalp-key ,v) ,v ,table))))

(defmacro has-key (k table)
  "Whether k is a key in the given hash-table."
  `(nth-value 1 (gethash ,k ,table)))

(defmethod mset-iterator ((set hash-set))
  (with-hash-table-iterator (iter (table set))
    #'(lambda ()
	(multiple-value-bind (exists k v) (iter)
	  (declare (ignore k))
	  (and exists v)))))  

(defmethod mset-member (elt (set hash-set))
  (has-key (equalp-key elt) (table set)))

(defmethod mset-size ((set hash-set))
  (hash-table-count (table set)))

;;; -------------------- Making sets --------------------

(defgeneric make-hash-set (arg)
  (:documentation
"arg may be an equalp hash-table, another kind of hash-table, a
sequence, a finite mset, or a single non-null element.  In the first
case, the function builds a new hash-set around the table (not a
copy).  Otherwise, the function dumps all the elements into a new
hash-set.  It returns the new hash-set."))

(defmethod make-hash-set ((table hash-table))
  (if (eq (hash-table-test table) 'equalp)
      (make-instance 'hash-set :table table)
    (let ((new-table (make-hash-table :test #'equalp
				      :size (hash-table-count table))))
      (maphash #'(lambda (k v)
		   (declare (ignore k))
		   (assert v () "Sorry, msets can't contain nil.")
		   (put-with-equalp-key v new-table))
	       table)
      (make-hash-set new-table))))

(defmethod make-hash-set ((arg sequence))
  (let ((table (make-hash-table :test #'equalp :size (length arg))))
    (map nil #'(lambda (elt)
		 (assert elt () "Sorry, msets can't contain nil.")
		 (put-with-equalp-key elt table))
	 arg)
    (make-hash-set table)))

(defmethod make-hash-set ((arg mset))
  (let ((n (mset-size arg)))
    (assert n (arg) "make-hash-set doesn't work on msets of unknown size.")
    (let ((table (make-hash-table :test #'equalp :size n)))
      (do-mset (elt arg (make-hash-set table))
	(put-with-equalp-key elt table)))))

(defmethod make-hash-set ((single-elt t))
  (let ((table (make-hash-table :test #'equalp :size 1)))
    (assert single-elt () "Sorry, msets can't contain nil.")
    (put-with-equalp-key single-elt table)
    (make-hash-set table)))

(defun iota (n)
  "Returns a lazy-set whose iterator returns 0, 1, ..., n-1 in
that order.  Returns an empty set if n is not a non-negative integer.
The name comes from APL, whose iota returned a vector with these same
elements."
  (let ((n0 (if (and (integerp n) (<= 0 n)) n 0)))
    (make-instance 'lazy-set
      :iterator-factory #'(lambda ()
			    (let ((i 0))
			      #'(lambda ()
				  (and (< i n0) (prog1 i (incf i))))))
      :containment-test #'(lambda (elt)
			    (and (integerp elt) (<= 0 elt) (< elt n0)))
      :size n0)))

(defun make-empty-set ()
  "Returns an empty lazy-set."
  (make-instance 'lazy-set
    :iterator-factory #'(lambda () #'(lambda () nil))
    :containment-test #'(lambda (elt) (declare (ignore elt)) nil)
    :size 0))

;;; ------------------------- Set theory -------------------------

(defun mset-emptyp (set)
  "Whether the given mset is empty."
  (aif (mset-size set) (zerop it) (null (mset-get-one-elt set))))

(defun mset-equal (set1 set2)
  "Whether two finite msets are equal.  Returns nil if either set
has size nil.
  The implementation checks whether the sets have the same size,
and if so then checks whether each element of set1 is in set2.
For good performance, therefore, set2 should have a fast
containment test."
  (let ((n1 (mset-size set1)))
    (when n1
      (let ((n2 (mset-size set2)))
	(when n2
	  (and (= n1 n2) (mset-subsetp set1 set2)))))))

(defmethod cat-equal-p ((s1 mset) (s2 mset))
  (mset-equal s1 s2))

(defgeneric mset-subset (pred set)
  (:documentation
"Returns the mset of all elements of 'set' satisfying pred."))

(defmethod mset-subset (pred (s mset))
  "Default implementation.  The return value is of class lazy-set.
Its size is non-nil if and only if the size of s is non-nil."
  (make-instance 'lazy-set
    :iterator-factory
    #'(lambda ()
	(let ((s-iter (mset-iterator s)))
	  #'(lambda ()
	      (do ((x (funcall s-iter) (funcall s-iter)))
		  ((or (null x) (funcall pred x))
		   x)))))
    :containment-test
    #'(lambda (elt)
	(and (funcall pred elt) (mset-member elt s)))
    :size
    (when (mset-size s)
      (mset-count-if pred s))))

(defmethod mset-subset (pred (set hash-set))
  "Returns a hash-set."
  (let ((subtable (make-hash-table :test #'equalp)))
    (maphash #'(lambda (k v)
		 (when (funcall pred v)
		   (puthash k v subtable)))
	     (table set))
    (make-hash-set subtable)))

(defgeneric mset-disjoint-union (set1 set2)
  (:documentation
"Union of two msets.  The caller must guarantee the union is really
disjoint; that is, the intersection of the sets must be empty."))

(defmethod mset-disjoint-union ((set1 mset) (set2 mset))
  "Default implementation.  The iterator goes through set1 first, then set2.
Returns a lazy-set."
  (make-instance 'lazy-set
    :iterator-factory
    #'(lambda ()
	(let ((iter1 (mset-iterator set1))
	      (iter2 (mset-iterator set2)))
	  #'(lambda ()
	      (or (funcall iter1) (funcall iter2)))))
    :containment-test
    #'(lambda (elt)
	(or (mset-member elt set1) (mset-member elt set2)))
    :size
    (let ((n1 (mset-size set1)))
      (when n1
	(let ((n2 (mset-size set2)))
	  (when n2
	    (+ n1 n2)))))))

(defmethod mset-disjoint-union ((set1 hash-set) (set2 hash-set))
  "Returns a hash-set."
  (let ((result (mset-union set1 set2)))
    (assert (= (mset-size result) (+ (mset-size set1) (mset-size set2))) ()
      "The union is not disjoint.")
    result))

(defun mset-intersection (set1 set2)
  "Intersection of two msets."
  (mset-subset #'(lambda (elt) (mset-member elt set2)) set1))

(defun mset-difference (set1 set2)
  "Difference set1 - set2 of two msets."
  (mset-subset #'(lambda (elt) (not (mset-member elt set2))) set1))

(defgeneric mset-union (set1 set2)
  (:documentation "Union of two msets."))

(defmethod mset-union ((set1 mset) (set2 mset))
  (mset-disjoint-union (mset-difference set1 set2) set2))

(defmethod mset-union ((set1 hash-set) (set2 hash-set))
  "Returns a hash-set."
  (let ((subtable (make-hash-table :test #'equalp)))
    (maphash #'(lambda (k v) (puthash k v subtable)) (table set1))
    (maphash #'(lambda (k v) (puthash k v subtable)) (table set2))
    (make-hash-set subtable)))

(defgeneric mset-exclusive-or (set1 set2)
  (:documentation "Exclusive or of two msets."))

(defmethod mset-exclusive-or ((set1 mset) (set2 mset))
  (mset-disjoint-union (mset-difference set1 set2)
		       (mset-difference set2 set1)))

(defmethod mset-exclusive-or ((set1 hash-set) (set2 hash-set))
  "Returns a hash-set."
  (let ((table1 (table set1))
	(table2 (table set2))
	(subtable (make-hash-table :test #'equalp)))
    (maphash #'(lambda (k v)
		 (unless (has-key k table2)
		   (puthash k v subtable)))
	     table1)
    (maphash #'(lambda (k v)
		 (unless (has-key k table1)
		   (puthash k v subtable)))
	     table2)
    (make-hash-set subtable)))

(defun mset-product-iterator (&rest msets)
  "Returns an iterator over the Cartesian product of one or more sets.
Each value returned by the iterator is a list (elt-0 elt-1 ...) where
elt-i is an element of the i-th set.  These lists may share structure,
so don't do destructive operations on them.  The values are returned
in column-major order--the elt-0's change the fastest, then the
elt-1's, etc."
  (if (endp msets)
      (error "Can't take the product of no sets.")
    (if (endp (rest msets))
	(let ((iter0 (mset-iterator (first msets))))
	  #'(lambda () ;; change elt-0 to (elt-0)
	      (aif (funcall iter0) (list it) nil)))
      (let ((iter1 (apply #'mset-product-iterator (rest msets)))
	    (tuple1 nil)
	    (iter0 nil))
	#'(lambda ()
	    (loop
	      (when (null tuple1)
		(setq tuple1 (funcall iter1))
		(if (null tuple1)
		    (return nil)
		  (setq iter0 (mset-iterator (first msets)))))
	      (aif (funcall iter0)
		   (return (cons it tuple1))
		(setq tuple1 nil))))))))

(defmethod print-object ((set mset) stream)
  (let ((i 0)
	(lim (or *print-length* 10)))
    (format stream "#<~S (" (type-of set))
    (do-mset (x set)
      (cond ((>= i lim)
	     (format stream " ...")
	     (return))
	    (t
	     (when (> i 0) (format stream " "))
	     (format stream "~S" x)
	     (incf i))))
    (format stream ")>")))

;;; ------------------------- Msets as sequences -------------------------

(defun mset-count-if (pred set)
  "Returns the number of items of the set satisfying pred."
  (let ((result 0))
    (do-mset (elt set result)
      (when (funcall pred elt)
	(incf result)))))

(defun mset-get-one-elt (set)
  "Returns the first element it finds in the set, or nil if it can't
find one."
  (do-mset (elt set nil)
    (return elt)))

(defun mset-find-if (pred set)
  "Returns the first element it finds that satisfies pred, or nil if
it can't find one."
  (do-mset (elt set nil)
    (when (funcall pred elt)
      (return elt))))

(defun mset-subsetp (set1 set2)
  "Whether set1 is a subset of set2."
  (do-mset (elt set1 t)
    (unless (mset-member elt set2)
      (return nil))))

(defun mset-some (pred set)
  "Whether at least one element of the set satisfies pred.  Compare
Lisp's 'some'."
  (do-mset (elt set nil)
    (awhen (funcall pred elt)
      (return it)))) ;; "some" returns it, not elt

(defun mset-every (pred set)
  "Whether every element of the set satisfies pred.  Compare
Lisp's 'every'."
  (do-mset (elt set t)
    (unless (funcall pred elt)
      (return nil))))

(defun mset-notany (pred set)
  "Whether every element of the set fails to satisfy pred.  Compare
Lisp's 'notany'."
  (do-mset (elt set t)
    (when (funcall pred elt)
      (return nil))))

(defun mset-notevery (pred set)
  "Whether at least one element of the set fails to satisfy pred.
Compare Lisp's 'notevery'."
  (do-mset (elt set nil)
    (unless (funcall pred elt)
      (return t))))

;;; ------------------------- Unit tests -------------------------

(in-package cl-user)

(let ((iota11 (iota 11)))
  (let ((countdown '()))
    (do-mset (i iota11) (push i countdown))
    (assert (equal countdown '(10 9 8 7 6 5 4 3 2 1 0))))
  (dotimes (i 11) (assert (mset-member i iota11)))
  (assert (not (mset-member 11 iota11)))
  (assert (not (mset-member 'pig iota11)))
  (assert (= 11 (mset-size iota11)))
  (assert (not (mset-emptyp iota11)))
  (let ((evens (mset-subset #'evenp iota11))
	(one3 (mset-subset #'(lambda (i) (= (mod i 3) 1)) iota11)))
    (macrolet ((ae (a b) `(assert (mset-equal ,a ,b))))
      (ae evens (make-hash-set '(0 2 4 6 8 10)))
      (ae one3 (make-hash-set '(1 4 7 10)))
      (ae (mset-intersection evens one3) (make-hash-set '(4 10)))
      (ae (mset-difference evens one3) (make-hash-set '(0 2 6 8)))
      (ae (mset-difference one3 evens) (make-hash-set '(1 7)))
      (ae (mset-union evens one3) (make-hash-set '(0 1 2 4 6 7 8 10)))
      (ae (mset-exclusive-or evens one3) (make-hash-set '(0 1 2 6 7 8))))
    (assert (not (mset-subsetp evens one3)))
    (assert (not (mset-subsetp one3 evens)))
    (assert (= (mset-count-if #'evenp one3) 2))))
  
(let ((ht (make-hash-table :test #'eql)))
  (dotimes (i 5)
    (puthash i i ht))
  (let ((set01234 (make-hash-set ht)))
    (dotimes (i 5) (assert (mset-member i set01234)))
    (assert (not (mset-member 5 set01234)))
    (do-mset (x set01234) (assert (and (<= 0 x) (< x 5))))
    (assert (= 5 (mset-size set01234)))
    (assert (mset-equal (iota 5) set01234))
    (assert (mset-equal set01234 (iota 5)))
    (assert (mset-equal (make-hash-set (vector 1 3 4 2 0)) set01234))
    (assert (not (mset-emptyp set01234)))
    (let ((set-1 '())
	  (prod-iter (mset-product-iterator set01234)))
      (awhile (funcall prod-iter)
	(push it set-1))
      (assert (equal (sort set-1 #'< :key #'first) '((0) (1) (2) (3) (4)))))
    (let ((set024 (mset-subset #'evenp set01234)))
      (do ((i 0 (+ i 2)))
	  ((> i 4))
	(assert (mset-member i set024)))
      (do-mset (x set024)
	(assert (member x '(0 2 4))))
      (assert (= 3 (mset-size set024)))
      (assert (mset-subsetp set024 set01234))
      (assert (not (mset-subsetp set01234 set024)))
      (let ((set13 (mset-difference set01234 set024)))
	(do ((i 1 (+ i 2)))
	    ((> i 3))
	  (assert (mset-member i set13)))
	(do-mset (x set13)
	  (assert (member x '(1 3))))
	(assert (= 2 (mset-size set13)))
	(assert (mset-subsetp set13 set01234))
	(assert (not (mset-subsetp set01234 set13)))
	(assert (mset-equal (mset-union set024 set13) set01234))
	(assert (mset-emptyp (mset-intersection set024 set13)))
	(assert (mset-equal (mset-disjoint-union set024 set13)
			    (mset-union set024 set13)))
	(assert (mset-equal (mset-disjoint-union set024 set13)
			    (mset-exclusive-or set024 set13)))
	(let ((set024-times-set13 '())
	      (prod-iter (mset-product-iterator set024 set13)))
	  (awhile (funcall prod-iter)
	    (push it set024-times-set13))
	  (assert (mset-equal (make-hash-set set024-times-set13)
			      (make-hash-set '((0 1) (2 1) (4 1)
					       (0 3) (2 3) (4 3)))))))
      (let ((singleton-0 (make-hash-set 0)))
	(assert (= 1 (mset-size singleton-0)))
	(assert (mset-subsetp singleton-0 set01234))
	(assert (not (mset-subsetp set01234 singleton-0)))
	(assert (mset-equal singleton-0 (make-hash-set singleton-0)))
	(assert (mset-equal (make-hash-set singleton-0) singleton-0))
	(assert (= 0 (mset-get-one-elt singleton-0)))
	(let ((singleton-2 (make-hash-set 2))
	      (singleton-4 (make-hash-set 4)))
	  (assert (mset-equal set024
			      (mset-union singleton-2
					  (mset-union singleton-0
						      singleton-4)))))))
    (assert (= (mset-count-if #'plusp set01234) 4))
    (assert (= (mset-find-if #'(lambda (x) (>= x 4)) set01234) 4))
    (assert (mset-some #'plusp set01234))
    (assert (mset-notevery #'plusp set01234))
    (assert (mset-every #'integerp set01234))
    (assert (mset-notany #'(lambda (x) (> x 10)) set01234))))    
