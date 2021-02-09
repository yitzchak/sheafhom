(in-package cl-user)

;;; ************************************************************

;;; THE CALLER SHOULD SET +nn+ [THE LEVEL N] AND RECOMPILE THIS CODE.
;;; Example in CMUCL:
;;; (defconstant +nn+ 42)
;;; (compile-file "p3" :load t :error-output nil)

;;; ************************************************************

(declaim (optimize speed))

(deftype mod-nn ()
  "The type of integers i with 0 <= i < nn."
  `(mod ,+nn+))

(deftype zero-to-nn ()
  "The type of integers i with 0 <= i <= nn."
  `(integer 0 ,+nn+))

(defun fac-inverse-array (mm)
  "Returns an array indexed by 0 through mm-1 whose i-th entry
is the inverse of i modulo mm, or is 0 if the inverse doesn't
exist.  mm can be composite.  mm must be >= 2."
  (let ((ans (make-array mm :initial-element 0)))
    (setf (svref ans 1) 1)
    (do ((i 2 (1+ i)))
	((= i mm) ans)
      (block one-i
	(when (and (zerop (svref ans i)) (= 1 (gcd mm i)))
	  (do ((j 2 (1+ j)))
	      ((= j mm) (error "Cannot invert ~D mod ~D." i mm))
	    (when (= 1 (mod (* i j) mm))
	      ;; Fill in table for i, j and their powers.
	      (do ((i-pwr i (mod (* i-pwr i) mm))
		   (j-pwr j (mod (* j-pwr j) mm)))
		  ((= i-pwr 1)
		   (return-from one-i))
		(when (zerop (svref ans i-pwr))
		  (setf (svref ans i-pwr) j-pwr
			(svref ans j-pwr) i-pwr))))))))))

(defparameter *inv-array* (fac-inverse-array +nn+)
  "An array of length +nn+ whose i-th entry is the inverse
of i modulo +nn+, or is 0 if the inverse doesn't exist.")

(defparameter *units-mod-nn*
    (let ((ans '()))
      (do ((i (1- +nn+) (1- i)))
	  ((= i 0))
	(unless (zerop (svref *inv-array* i))
	  (push i ans)))
      (assert (= (totient +nn+) (length ans)) ()
	"Wrong number of units mod ~D: expected ~D, got ~D, viz.:~&~A."
	+nn+ (totient +nn+) (length ans) ans)
      ans)
  "A list of the units mod +nn+.  E.g., if +nn+ = 12, this is (1 5 7 11).")

(defmacro modulo-nn (a)
  `(the mod-nn (mod ,a +nn+)))

(defun proj-nice (x)
  "x is a list of fixnums.  The output is a list of mod-nn's that
is a scalar multiple of x by a unit of Z/nnZ, chosen to be
lexicographically the least among all such multiples."
  (declare (list x))
  (labels ((proj-nice-aux (back rfront units)
	     (declare (list back rfront units))
	     (cond ((endp (rest units))	; units = '(1) ==> done
		    (nreconc rfront back))
		   ((endp back)
		    (error "Was given a non-primitive vector."))
		   (t
		    (let ((x (first back))
			  (new-units '())
			  (min-xu +nn+))
		      (declare (type mod-nn x) (list new-units)
			       (type zero-to-nn min-xu))
		      ;; As u runs through "units", find the minimum
		      ;; least positive residue of xu, and all u
		      ;; attaining that minimum.  The latter u will
		      ;; comprise new-units.
		      (dolist (u units)
                        (declare (type mod-nn u))
			(let ((xu (modulo-nn (* x u))))
			  (declare (type mod-nn xu))
			  (cond ((< xu min-xu)
				 (setq new-units (list u)
				       min-xu xu))
				((= xu min-xu)
				 (push u new-units)))))
		      (let* ((u (first new-units))
			     (uinv (the mod-nn (svref *inv-array* u)))
			     (new-back
			      (mapcar #'(lambda (b)
					  (declare (type mod-nn b))
					  (modulo-nn (* u b)))
				      back)))
			(declare (type mod-nn u uinv) (list new-back))
			(proj-nice-aux
			 (rest new-back)
			 (cons (first new-back) rfront)
			 (mapcar #'(lambda (v)
				     (declare (type mod-nn v))
				     (modulo-nn (* uinv v)))
				 new-units))))))))
    (proj-nice-aux
     (mapcar #'(lambda (a) (modulo-nn a)) x) '() *units-mod-nn*)))

(defun is-proj-nice-p (x)
  "Outputs t iff x is a tuple that could be the output of proj-nice.
Assumes all entries of the input are already of type mod-nn."
  (declare (list x))
  (labels ((is-proj-nice-p-aux (back rfront units)
	     (declare (list back rfront units))
	     (cond ((endp (rest units)) ; units = '(1) ==> done
		    t)
		   ((endp back) ; non-primitive
		    nil)
		   (t
		    (let ((x (first back))
			  (new-units '())
			  (min-xu +nn+))
		      (declare (type mod-nn x) (list new-units)
			       (type zero-to-nn min-xu))
		      ;; As u runs through "units", find the minimum
		      ;; least positive residue of xu, and all u
		      ;; attaining that minimum.  The latter u will
		      ;; comprise new-units.
		      (dolist (u units)
                        (declare (type mod-nn u))
			(let ((xu (modulo-nn (* x u))))
			  (declare (type mod-nn xu))
			  (cond ((< xu min-xu)
				 (setq new-units (list u)
				       min-xu xu))
				((= xu min-xu)
				 (push u new-units)))))
		      (setq new-units (nreverse new-units))
		      ;; they are still sorted by <
		      (if (not (= 1 (the mod-nn (first new-units))))
			  nil
			(is-proj-nice-p-aux
			 (rest back)
			 (cons (first back) rfront)
			 new-units)))))))
  (is-proj-nice-p-aux x '() *units-mod-nn*)))

;;; -------------------- Unit Tests --------------------

(assert (equalp (fac-inverse-array 11)
		(make-array 11 :initial-contents
			    '(0 1 6 4 3 9 2 8 7 5 10))))

(assert (equalp (fac-inverse-array 12)
		(make-array 12 :initial-contents
			    '(0 1 0 0 0 5 0 7 0 0 0 11))))
