(in-package shh2)

(declaim (optimize speed))

(defvar *prime-vector*
  (make-array 2 :element-type '(integer 2 *) :initial-contents '(2 3)
	      :adjustable t :fill-pointer t)
  "All the primes 2,3,5,... that Sheafhom has discovered so far.
The recommended way to use this data is through the mset *primes*,
with code like
 (do-mset (p *primes*) ...).")

(defvar *primes*
  (make-instance 'lazy-set
    :iterator-factory
    #'(lambda () ;; iterator-factory
	(let ((i 0))
	  (declare (fixnum i))
	  #'(lambda () ;; iterator
	      (let ((ans (aref *prime-vector* i))
		    (len (length *prime-vector*)))
		(declare (type nnfixnum len))
		(when (= i (the fixnum (1- len)))
		  (labels ((next-prime (n)
			     "The next prime > the positive odd integer n."
			     (declare (type (integer 3 *) n))
			     (do ((q (+ n 2) (+ q 2)))
				 (nil)
			       (declare (type (integer 5 *) q))
			       (do ((j 1 (1+ j)))
				   ((= j len)
				    ;; If you get here, two
				    ;; consecutive primes p, q satisfy
				    ;; q > p^2.  This can't happen,
				    ;; because Bertrand's postulate
				    ;; [Hardy and Wright, Theorem 418]
				    ;; guarantees q < 2p.
				    (error "Error in next-prime."))
				 (declare (fixnum j))
				 (let ((p (aref *prime-vector* j)))
				   (declare (type (integer 3 *) p))
				   (when (> (* p p) q)
				     (return-from next-prime q))
				   (when (zerop (rem q p))
				     (return nil)))))))
		    (vector-push-extend (next-prime ans) *prime-vector*)))
		(incf i)
		ans))))
    :containment-test
    #'(lambda (x) (and (integerp x) (>= (the integer x) 2) (primep x)))
    :size
    nil)
  "The infinite set of positive prime integers.  The iterator
returns them in order by <.  We compute them by the Sieve of Eratosthenes,
lazily, with sublime indifference to efficiency.")

(defun primep (x)
  "Whether the absolute value of x is a prime in the integers."
  (if (not (integerp x))
      nil
    (let ((n (abs x)))
      (declare (integer n))
      (let ((last-p (aref *prime-vector* (1- (length *prime-vector*)))))
	(declare (type (integer 3 *) last-p))
	(cond ((= n last-p)
	       t)
	      ((< n last-p)
	       (>= (the integer (bsearch-integer n *prime-vector*)) 0))
	      (t
	       (do-mset (p *primes*)
		 (declare (type (integer 2 *) p))
		 (when (> (the integer (* p p)) n)
		   (return t))
		 (when (zerop (rem n p))
		   (return nil)))))))))

(defun bsearch-integer (x vec)
  "Searches for the integer x in the vector vec of integers.  The vector
must be sorted by <.  Returns the index of x, if it is found.  Otherwise,
returns -insertionpoint-1."
  (declare (integer x) (vector vec))
  (do ((low 0)
       (high (1- (length vec))))
      ((> low high) ;; x not found
       (- (1+ low))) ;; may not be a fixnum
    (declare (fixnum low high))
    (let ((mid (floor (+ low high) 2)))
      (declare (type nnfixnum mid))
      (let ((y (aref vec mid)))
	(declare (integer y))
	(cond ((= y x) ;; x found
	       (return mid))
	      ((< y x)
	       (setq low (1+ mid)))
	      (t ;; y > x
	       (setq high (1- mid))))))))

;;; ------------------------------------------------------------

(defun valuation (n p &optional (e 0))
  "Returns two values, e and n/(p^e), where e is the number of times p
divides n.  Here n and p must be non-zero integers.  Normally p is a
prime, and e is then called the additive valuation of n at p."
  (declare (integer n p e))
  (multiple-value-bind (q r) (floor n p)
    (declare (integer q r))
    (if (zerop r)
	(valuation q p (1+ e))
      (values e n))))

(defun factor (n)
  "Returns the prime factorization [p1^e1 * p2^e2 * ...] of n, as a list
 ((p1 . e1) (p2 . e2) ...).  Here n must be an integer.  The p's are
primes satisfying 2 <= p1 < p2 < ..., and the e's are >= 1.  The method
is trial division.  If n < 0, the sign is ignored.  If n = 0, an error
is signaled."
  (declare (integer n))
  (assert (not (zerop n)) (n) "Can't factor 0.")
  (if (< n 0)
      (factor (- n))
    (let ((ans '()))
      (do-mset (p *primes*)
	(declare (type (integer 2 *) p))
	(cond ((= n 1)
	       (return-from factor (nreverse ans)))
	      ((> (the integer (* p p)) n)
	       (return-from factor (nreconc ans (list (cons n 1)))))
	      (t
	       (multiple-value-bind (e new-n) (valuation n p)
		 (declare (integer e new-n))
		 (when (> e 0)
		   (push (cons p e) ans)
		   (setq n new-n)))))))))

(defun is-power-of (n p)
  "If there is an e with n = p^e, return e, and otherwise return nil.
Here n and p must be integers."
  (declare (integer n p))
  (multiple-value-bind (e r) (valuation n p)
    (declare (integer e r))
    (if (= r 1) e nil)))

(defun totient (n &optional (fac (factor n)))
  "The Euler phi-function of n.  Here n must be an integer.  If the
second argument is provided, it should be the prime factorization
of n as found by (factor n)."
  (declare (integer n))
  (dolist (pe fac n)
    (let ((p (car pe)))
      (declare (integer p))
      (setq n (* (the integer (truncate n p)) (the integer (1- p)))))))

(defun ext-gcd (a b)
  "Given integers a, b, returns three values u, v, d, such that
d is the non-negative gcd of a and b, and a*u + b*v = d."
  (declare (integer a b))
  (if (or (< a 0) (< b 0))
      (multiple-value-bind (u v d) (ext-gcd (abs a) (abs b))
	(declare (integer u v d))
	(values (if (< a 0) (- u) u) (if (< b 0) (- v) v) d))
    (labels ((eg-aux (a b u v w x)
	       (declare (type (integer 0 *) a b) (integer u v w x))
	       ;; Non-negative row vector [a b], and matrix
	       ;; [u w]
	       ;; [v x]
	       ;; of determinant +/- 1.
	       (if (< a b)
		   (eg-aux b a w x u v)
		 (if (= b 0)
		     (values u v a)
		   (multiple-value-bind (q r) (floor a b)
		     (declare (integer q r))
		     (eg-aux b r w x (- u (* q w)) (- v (* q x))))))))
      (eg-aux a b 1 0 0 1))))

(defun inv-mod (a n)
  "The multiplicative inverse of a mod n, in the range [1,n).  Here a
and n must be integers, with n positive.  Signals an error if a is not
invertible mod n."
  (declare (integer a n))
  (assert (> n 0) (n) "n = ~D must be positive." n)
  (multiple-value-bind (u v d) (ext-gcd a n)
    (declare (integer u d) (ignore v))
    (if (= d 1)
	(mod u n)
      (assert nil (a) "~A is not invertible modulo ~A." a n))))

(defun power-mod (a i n &optional (ans 1))
  "Finds a^i mod n, in the range [0,n), by a binary powering algorithm.
Here a, i and n must be integers, with n positive."
  (declare (integer a i n ans))
  (assert (> n 0) (n) "n = ~D must be positive." n)
  (cond ((< i 0)
	 (power-mod (inv-mod a n) (- i) n ans))
	((= i 0)
	 ans)
	(t
	 (multiple-value-bind (q r) (floor i 2)
	   (declare (integer q) (type (integer 0 1) r))
	   (power-mod (mod (the integer (* a a)) n)
		      q n
		      (if (= r 0) ans (mod (the integer (* a ans)) n)))))))
		 
(defun primitive-root (p)
  "Returns the smallest positive primitive root mod the prime integer p."
  (declare (integer p))
  (assert (primep p) (p) "~A is not prime." p)
  (if (< p 0)
      (primitive-root (- p))
    (if (= p 2)
	1
      (let* ((n (1- p))
	     (pwr-list (mapcar #'(lambda (pe)
				   (truncate n (the integer (car pe))))
			       (factor n))))
	(declare (type (integer 2 *) n))
	(do ((a 2 (1+ a)))
	    ((= a p) (assert nil () "No primitive root found mod ~A." p))
	  (declare (type (integer 2 *) a))
	  (block this-a
	    (dolist (k pwr-list (return-from primitive-root a))
	      (when (= 1 (power-mod a k p))
		(return-from this-a)))))))))

(defun quad-residue (a b &optional (ans 1))
  "Finds the quadratic residue symbol (a | b).  Here a and b must be
integers with b odd.  (2 | b) means (-1)^((b^2-1)/8).  Returns 1 or -1,
or returns 0 if the inputs are not relatively prime."
  (declare (integer a b) (type (integer -1 1) ans))
  (assert (oddp b) (b) "(a | b) is undefined because b = ~A is even." b)
  (cond ((< b 0)
	 (quad-residue a (- b) ans))
	((< a 0)
	 (quad-residue (- a) b (if (= (mod b 4) 3) (- ans) ans)))
	((>= a b)
	 (quad-residue (mod a b) b ans))
	((= a 0)
	 0)
	((= 0 (mod a 4))
	 (quad-residue (truncate a 4) b ans))
	((evenp a)
	 (quad-residue (truncate a 2) b
		       (case (mod b 8) ((3 5) (- ans)) (t ans))))
	((= a 1)
	 ans)
	(t
	 (quad-residue b a (if (and (= (mod a 4) 3) (= (mod b 4) 3))
			       (- ans)
			     ans)))))

;;; ------------------------- Unit tests -------------------------

(let ((primes-to-50 '()))
  (do-mset (p *primes*)
    (if (> p 50)
	(return)
      (push p primes-to-50)))
  (assert (equal (nreverse primes-to-50)
		 '(2 3 5 7 11 13 17 19 23 29 31 37 41 43 47))))
(let ((primes-4kplus1 (mset-subset #'(lambda (p) (= (mod p 4) 1)) *primes*)))
  (assert (mset-member 17 primes-4kplus1))
  (assert (not (mset-member 19 primes-4kplus1)))
  (assert (not (mset-member 499 primes-4kplus1))))
(assert (not (primep 5616)))
(assert (not (primep (* 29 31))))
(assert (equal (factor 1) '()))
(assert (equal (factor 2) '((2 . 1))))
(assert (equal (factor 32) '((2 . 5))))
(assert (equal (factor 257) '((257 . 1))))
(assert (equal (factor 360) '((2 . 3) (3 . 2) (5 . 1))))
(assert (equal (factor 4096) '((2 . 12))))
(assert (equal (factor 2197) '((13 . 3))))
(assert (equal (factor 5616) '((2 . 4) (3 . 3) (13 . 1))))
(assert (null (factor 1)))
(assert (is-power-of 32 2))
(assert (is-power-of 257 257))
(assert (is-power-of 2197 13))
(assert (not (is-power-of 96 2)))
(assert (not (is-power-of 2197 3)))
(assert (= (totient 360) (* 2 2 1 3 2 4)))
(assert (= (totient 5616) (* 2 2 2 1 3 3 2 12)))
(multiple-value-bind (u v d) (ext-gcd 4554 -3453)
  (assert (= d 3))
  (assert (= u 69))
  (assert (= v 91))
  (assert (= (+ (* 69 4554) (* 91 -3453)) 3)))
(multiple-value-bind (u v d) (ext-gcd 5616 168)
  (assert (= d 24))
  (assert (= u -2))
  (assert (= v 67))
  (assert (= (+ (* -2 5616) (* 67 168)) 24)))
(assert (equal (mapcar #'(lambda (a) (inv-mod a 5)) '(1 2 3 4)) '(1 3 2 4)))
(assert (= 11 (inv-mod 3 16)))
(assert (= 3 (inv-mod 11 16)))
(assert (equal (mapcar #'(lambda (a) (power-mod a 2 7)) '(0 1 2 3 4 5 6))
	       '(0 1 4 2 2 4 1)))
(assert (equal (mapcar #'(lambda (a) (power-mod a 3 7)) '(0 1 2 3 4 5 6))
	       '(0 1 1 6 1 6 6)))
(dotimes (a 23) (assert (= (power-mod a 23 23) a)))
(assert (equal (mapcar #'primitive-root '(2 3 5 7 11 13 17))
	       '(1 2 2 3 2 2 3)))
(dolist (b '(37 41 43 101))
  (let ((all-units '())
	(square-units '())
	(phi (totient b)))
    (dotimes (a b)
      (when (= 1 (gcd a b))
	(push a all-units)
	(pushnew (mod (* a a) b) square-units :test #'=)))
    (assert (= phi (length all-units)))
    (assert (= phi (* 2 (length square-units))))
    (let ((all-u-set (make-hash-set all-units))
	  (sq-u-set (make-hash-set square-units)))
      (let ((non-sq-u-set (mset-difference all-u-set sq-u-set)))
	(do-mset (a sq-u-set)
	  (assert (= 1 (quad-residue a b))))
	(do-mset (a non-sq-u-set)
          (assert (= -1 (quad-residue a b))))
	(dotimes (i b)
	  (let ((ct 0))
	    (when (mset-member i sq-u-set)
	      (incf ct))
	    (when (mset-member i non-sq-u-set)
	      (incf ct))
	    (when (= 0 (quad-residue i b))
	      (incf ct))
	    (assert (= 1 ct))))))))
