(in-package cl-user)

;;; ************************************************************

;;; THE CALLER SHOULD SET +nn+ [THE LEVEL N], RECOMPILE p3.lisp
;;; AND cardp3.lisp, AND RECOMPILE THIS CODE.
;;; Example in CMUCL:
;;; (defconstant +nn+ 42)
;;; (compile-file "p3" :load t :error-output nil)
;;; (compile-file "cardp3" :load t :error-output nil)
;;; (compile-file "eqco4N" :load t :error-output nil)

;;; ************************************************************

;;; These programs compute the rank of H^5 and H^6 for Gamma_0(N)
;;; in SL_4(Z).  They compute the Gamma_0(N)-equivariant cohomology of
;;; the well-rounded retract.

;;; These are based on the GL programs written in July '93 from notes by
;;; Avner dated June 15, 1993.  However, the current version uses my own
;;; working-out of the equations, in notes from Jan-Apr '94 which
;;; follow Ken Brown's book, VII.7-8.  This SL version was kludged up
;;; in June '94, by replacing gl4dat.lsp with sl4dat.lsp and improving
;;; memory usage.  Further improvements in space and time performance
;;; were made in Sept '94.  The change from equivariant homology to
;;; equivariant cohomology was made in October 1998.  The change from
;;; prime level p to composite level N was made in May 1999.

;;; Before each use, set the constant +nn+ (= N) to the desired value,
;;; recompile p3, recompile this file, and call the main function
;;; as follows:
;;;   (h5)

;;; This version's immediate predecessor is sl4dump.lsp, from the fall
;;; of 1994.  It uses the homolalg portions of my system Sheafhom.  It
;;; dumps the big matrices in a form Sheafhom can use, and relies on
;;; Sheafhom to find bases for the cocycles.

(declaim (optimize speed))

;;; We use points in P^3 over Z/nnZ.  We represent these in two
;;; equivalent ways.  A PPT is a four-element list, as produced by
;;; PROJ-NICE.  A CPT is an integer in the range 0 <= i < +cardP3+.
;;; Here are the tables and functions which define their
;;; relationship.

(defvar *ppt-table*)

(defvar *cpt-table*)

(deftype cpt () `(mod ,+cardP3+))

(defvar *print-projective-points* nil)

(defvar *cpt-set*)

;;; The function h5 will call this, then set the -table variables to
;;; nil when it's done.

(defun initialize-ppt-and-cpt-tables ()
  (when *print-projective-points*
    (format t "~&Printing projective points.~&~D" +cardP3+))
  (excl:tenuring ;; not ANSI CL
   (setq *ppt-table* (make-hash-table :test #'equal :size +cardP3+)
	 *cpt-table* (make-array +cardP3+)
	 *cpt-set* (make-array +cardP3+ :element-type 'bit)))
  (let ((kk 0))
    (declare (fixnum kk))
    (excl:tenuring ;; not ANSI CL
     (dotimes (x0 +nn+)
       (declare (type zero-to-nn x0))
       (let ((g0 (gcd +nn+ x0)))
	 (declare (type zero-to-nn g0))
	 (dotimes (x1 +nn+)
	   (declare (type zero-to-nn x1))
	   (let ((g1 (gcd g0 x1)))
	     (declare (type zero-to-nn g1))
	     (dotimes (x2 +nn+)
	       (declare (type zero-to-nn x2))
	       (let ((g2 (gcd g1 x2)))
		 (declare (type zero-to-nn g2))
		 (dotimes (x3 +nn+)
		   (declare (type zero-to-nn x3))
		   (let ((g3 (gcd g2 x3)))
		     (declare (type zero-to-nn g3))
		     (let ((x (list x0 x1 x2 x3)))
		       (when (and (= g3 1) (is-proj-nice-p x))
			 (setf (gethash x *ppt-table*) kk)
			 (setf (svref *cpt-table* kk) x)
			 (when *print-projective-points*
			   (format t "~&~D ~D ~D ~D" x0 x1 x2 x3))
			 (incf kk))))))))))))
    (assert (= kk +cardP3+) ()
      "Error initializing *ppt-table* and *cpt-table*: count is off.")))	

(defmacro ppt-to-cpt (x)
  `(the cpt (gethash (the list ,x) *ppt-table*)))

(defmacro cpt-to-ppt (j)
  `(the list (svref *cpt-table* (the cpt ,j))))

(defun fill-cpt-set ()
  (fill (the simple-bit-vector *cpt-set*) 1))

(defun next-in-cpt-set ()
  (position-if #'(lambda (b) (declare (bit b)) (= b 1))
	       (the simple-bit-vector *cpt-set*)))

;;; sl4dat defines variables  stab*  which represent the stablizer
;;; subgroups of a cell in the SL_4 well-rounded retract, together
;;; with the orientation character for the cell.  Each  stab*  is a
;;; list of  ((col col col col) . s) , where the first entry is a 4-by-4
;;; matrix stored by columns, and the second is the orientation
;;; character.  The matrices form coset rep's of the stabilizer
;;; subgroup mod +/- I.  The matrices act on the C-configurations as
;;; column vectors, and (therefore) on the points of P^3(Z/nnZ) as row
;;; vectors.  The file also defines stab__int__ , the intersection of
;;; various of the stab's.  With each call to h5, these variables are
;;; defined, then set to nil when they are no longer needed.

(defvar stab6)
(defvar stab5a)
(defvar stab5b)
(defvar stab5btw)
(defvar stab5c)
(defvar stab4a)
(defvar stab4b)
(defvar stab4c)
(defvar stab4d)
(defvar stab6int5a)
(defvar stab6int5b)
(defvar stab6int5c)
(defvar stab5aint4a)
(defvar stab5aint4b)
(defvar stab5aint4c)
(defvar stab5bint4a)
(defvar stab5btwint4b)
(defvar stab5bint4d)
(defvar stab5cint4b)

;;; The next variable will be often used and reset when we assign code
;;; numbers to the orbits.
(defvar kount)
(declaim (fixnum kount))

(defconstant gamma5b4b '((0 0 -1 0) (0 0 0 -1) (1 0 1 1) (0 1 0 0)))
  ;; A list (col col col col).

(defvar *print-orbits* nil)
(defvar whole-orbit-list '())

(defvar *eqco4n-output* t
  "A stream where (h5) will print the H^5 cocycles in column-major
order.  Defaults to standard output.")

(defmacro make-sp (index value)
  `(funcall +make-sp+ ,index ,value))

;;; Unit test of Wiedemann methods, for want of a better place to put it.
;;; Only tests non-maximal rank.
(when (sp-f_p-p (make-sp -1 1))
  (do ((n 1 (1+ n)))
      ((> n 20))
    (declare (type nnfixnum n))
    (do ((rk 1 (1+ rk)))
	((>= rk n))
      (declare (type nnfixnum rk))
      (shh2::wiedemann-square-test n rk +make-sp+))))

;;; Here is the main routine.

(defun h5 ()
  (format t "~&##### Program gunnlSL4.  Level N = ~D. #####~&" +nn+)
  (excl:tenuring ;; not ANSI CL
   (load "sl4dat" :verbose nil))
  (initialize-ppt-and-cpt-tables)
  (let (oreps6 oreps5a oreps5b oreps5c oreps4a oreps4b oreps4c oreps4d
	(pt-to-code-5a (make-array +cardP3+))
	(pt-to-code-5b (make-array +cardP3+))
	(pt-to-code-5c (make-array +cardP3+))
	(pt-to-code-4a (make-array +cardP3+))
	(pt-to-code-4b (make-array +cardP3+))
	(pt-to-code-4c (make-array +cardP3+))
	(pt-to-code-4d (make-array +cardP3+))
	;; Given a CPT x, (svref pt-to-orep-.. x) is the CPT that
	;; represents x's orbit in the oreps.. lists.
	(pt-to-orep-5a (make-array +cardP3+))
	(pt-to-orep-5b (make-array +cardP3+))
	(pt-to-orep-5c (make-array +cardP3+))
	(pt-to-orep-4a (make-array +cardP3+))
	(pt-to-orep-4b (make-array +cardP3+))
	(pt-to-orep-4c (make-array +cardP3+))
	(pt-to-orep-4d (make-array +cardP3+))
	proto-row
	(n5 0)
	(n4 0))
    (declare (type (or simple-vector null)
		   pt-to-code-5a pt-to-code-5b pt-to-code-5c
		   pt-to-code-4a pt-to-code-4b pt-to-code-4c
		   pt-to-code-4d
		   pt-to-orep-5a pt-to-orep-5b pt-to-orep-5c
		   pt-to-orep-4a pt-to-orep-4b pt-to-orep-4c
		   pt-to-orep-4d)
             (fixnum n5 n4))
    (format t "~&Creating orbits of type 6.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps6  (parse stab6  nil nil '()))
    (setq kount 0)
    (when *print-orbits*
      (format t "~&~S" (nreverse whole-orbit-list))) ; nreverse imp't!
    (format t "~&Creating orbits of type 5a.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps5a (parse stab5a pt-to-code-5a pt-to-orep-5a '()))
    (when *print-orbits*
      (format t "~&~S" (nreverse whole-orbit-list)))
    (format t "~&Creating orbits of type 5b.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps5b (parse stab5b pt-to-code-5b pt-to-orep-5b '()))
    (when *print-orbits*
      (format t "~&~S" (nreverse whole-orbit-list)))
    (format t "~&Creating orbits of type 5c.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps5c (parse stab5c pt-to-code-5c pt-to-orep-5c '()))
    (setq n5 kount)
    (setq kount 0)
    (when *print-orbits*
      (format t "~&~S" (nreverse whole-orbit-list)))
    (format t "~&Creating orbits of type 4a.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps4a (parse stab4a pt-to-code-4a pt-to-orep-4a '()))
;    (format t "~&~S" (nreverse whole-orbit-list))
    (format t "~&Creating orbits of type 4b.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps4b (parse stab4b pt-to-code-4b pt-to-orep-4b '()))
;    (format t "~&~S" (nreverse whole-orbit-list))
    (format t "~&Creating orbits of type 4c.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps4c (parse stab4c pt-to-code-4c pt-to-orep-4c '()))
;    (format t "~&~S" (nreverse whole-orbit-list))
    (format t "~&Creating orbits of type 4d.~&")
    (when *print-orbits* (setq whole-orbit-list '()))
    (fill-cpt-set)
    (setq oreps4d (parse stab4d pt-to-code-4d pt-to-orep-4d '()))
    (setq n4 kount)
;    (format t "~&~S" (nreverse whole-orbit-list))
    (format t "~&End of all the orbit lists.~&")
    (setq *cpt-set* nil)
    ;; At this point, each elt of oreps5x is a point of P^3
    ;; representing a single class of 5-cells of type 5x in
    ;; Gamma_0(N)\G/K.  Choosing an elt of the orbit chooses an
    ;; orientation on the cell, namely the orientation given by the
    ;; sign assoc. to the elt.  The given rep've point has sign +1.
    ;; The class has a unique code number,  assigned to it by kount.
    ;; It represents a one-dimensional summand H^0(stab5x, C_sigma) in
    ;; the E^1 term of Brown's homology spectral sequence.  There are
    ;; other classes of 5-cells, but they contribute 0 to the E^1 term
    ;; and therefore have been removed. Similar remarks apply to 6-
    ;; and 4x-cells.
    ;;    Next, set up the equations.
    (let* ((blank-array (make-array (max n5 n4)))
	   (n6 (length oreps6))
	   (h5-mat (make-csparse-zero n5 n4))
	   (h6-mat (make-csparse-zero n6 n5)))
      (declare (simple-vector blank-array) (type nnfixnum n6))
      (setq kount 0) ; at the start of each matrix
      (format t "~&Setting up h6-mat.~&")
      (dolist (orep oreps6)
	(declare (type cpt orep))
	(setq proto-row (append
			 (fac-d1 orep oreps5a pt-to-code-5a pt-to-orep-5a
				 stab6 stab5a stab6int5a)
			 (fac-d1 orep oreps5b pt-to-code-5b pt-to-orep-5b
				 stab6 stab5b stab6int5b)
			 (fac-d1 orep oreps5c pt-to-code-5c pt-to-orep-5c
				 stab6 stab5c stab6int5c)))
	(dolist (pair (code-and-sign-collapse proto-row blank-array n5))
	  (csparse-set h6-mat (make-sp kount (cdr pair)) (the fixnum (car pair))))
	(incf kount))
      (setq stab6 nil
	    stab6int5a nil
	    stab6int5b nil
	    stab6int5c nil
	    pt-to-code-5a nil
	    pt-to-orep-5a nil
	    pt-to-code-5b nil
	    pt-to-orep-5b nil
	    pt-to-code-5c nil
	    pt-to-orep-5c nil
	    oreps6 nil)
      (setq kount 0)
      (format t "~&Setting up h5-mat (5a).~&")
      (dolist (orep oreps5a)
	(declare (type cpt orep))
	(setq proto-row (append
			 (fac-d1 orep oreps4a pt-to-code-4a pt-to-orep-4a
				 stab5a stab4a stab5aint4a)
			 (fac-d1 orep oreps4b pt-to-code-4b pt-to-orep-4b
				 stab5a stab4b stab5aint4b)
			 (fac-d1 orep oreps4c pt-to-code-4c pt-to-orep-4c
				 stab5a stab4c stab5aint4c)))
	(dolist (pair (code-and-sign-collapse proto-row blank-array n4))
	  (csparse-set h5-mat (make-sp kount (cdr pair)) (the fixnum (car pair))))
	(incf kount))
      (setq stab5a nil
	    stab4c nil
	    stab5aint4a nil
	    stab5aint4b nil
	    stab5aint4c nil
	    pt-to-code-4c nil
	    pt-to-orep-4c nil
	    oreps5a nil
	    oreps4c nil)
      (format t "~&Setting up h5-mat (5b).~&")
      (dolist (orep oreps5b)
	(declare (type cpt orep))
	(setq proto-row
	  (append
	   (fac-d1 orep oreps4a pt-to-code-4a pt-to-orep-4a
		   stab5b stab4a stab5bint4a -1)
	   (fac-d1 (ppt-to-cpt
		    (proj-nice
		     (mapcar #'(lambda (col)
				 (the fixnum
				   (list-dot (cpt-to-ppt orep) col)))
					; inefficient; this ^^^ should be
					; computed only once
			     gamma5b4b)))
		   oreps4b
		   pt-to-code-4b
		   pt-to-orep-4b
		   stab5btw
		   stab4b
		   stab5btwint4b
		   +1)			; by p. 21
	   (fac-d1 orep oreps4d pt-to-code-4d pt-to-orep-4d
		   stab5b stab4d stab5bint4d)))
	(dolist (pair (code-and-sign-collapse proto-row blank-array n4))
	  (csparse-set h5-mat (make-sp kount (cdr pair)) (the fixnum (car pair))))
	(incf kount))
      (setq stab5b nil
	    stab4a nil
	    stab4d nil
	    stab5bint4a nil
	    stab5btw nil
	    stab5btwint4b nil
	    stab5bint4d nil
	    pt-to-code-4a nil
	    pt-to-orep-4a nil
	    pt-to-code-4d nil
	    pt-to-orep-4d nil
	    oreps5b nil
	    oreps4a nil
	    oreps4d nil)
      (format t "~&Setting up h5-mat (5c).~&")
      (dolist (orep oreps5c)
	(declare (type cpt orep))
	(setq proto-row (fac-d1 orep oreps4b pt-to-code-4b pt-to-orep-4b
				stab5c stab4b stab5cint4b -1))
	(dolist (pair (code-and-sign-collapse proto-row blank-array n4))
	  (csparse-set h5-mat (make-sp kount (cdr pair)) (the fixnum (car pair))))
	(incf kount))
      (setq stab5c nil
	    stab4b nil
	    stab5cint4b nil
	    pt-to-code-4b nil
	    pt-to-orep-4b nil
	    oreps5c nil
	    oreps4b nil)
      ;; Done
      (clrhash *ppt-table*) ;; gc-help
      (fill *cpt-table* '()) ;; gc-help
      (setq proto-row '()) ;; gc-help
      (setq *ppt-table* nil
	    *cpt-table* nil)
      (format t "~&Testing del del = 0 ...")
      (assert (m-product-zerop h6-mat h5-mat) ()
	"del del /= 0")
      (format t " OK.")
      ;; The 1999 version dumped the matrices at this point and exited.
      ;; The code here does the same as the version demoed to Avner in
      ;; the Boston Public Garden in April 2004, but without
      ;; the categorical framework of qvsp-morphisms.
      #|
      (format t "~&Map C^5 --> C^6 is ~S~&" h6-mat)
      (unless +only-d5+
	(format t "~&Map C^4 --> C^5 is ~S~&" h5-mat))
      (format t "~&Computing SNF of C^5 --> C^6 ...~&")
      (let* ((h6-mat-copy (csparse-copy h6-mat)) ;; debug line
	     (snf6 (let ((*verbose* +only-d5+))
		     (make-snf h6-mat nil t t t)))
	     (h6 (- (m-num-rows h6-mat) (rank snf6))))
	(format t "~&H^6(..., Z) HAS RANK ~D~&" h6)
	(format t "~&H^6(..., Z) HAS TORSION ~S~&"
		(mapcar #'abs (torsion snf6)))
	(format t "~&Creating ker(C^5 --> C^6), which will be ~D by ~D ... with ~D Q's~&"
		(m-num-cols h6-mat)
		(- (m-num-cols h6-mat) (rank snf6))
		(length (slot-value snf6 'shh2::q-list)))
	(setq h6-mat nil) ;; release to GC
	(let ((ker6 (let ((*show-stats* +only-d5+))
		      (shh2::m-ker snf6))))
	  (declare (type csparse ker6))
	  (format t "~&Creating kerRetraction(C^5 --> C^6) ...~&")
	  (let ((ker-ret6 (shh2::m-ker-retraction snf6)))
	    (declare (type csparse ker-ret6))
	    (when +only-d5+
	      (return-from h5))
	    (setq snf6 nil) ;; release to GC
	    (format t "~&Computing map f : C^4 --> ker ...~&")
	    (let ((f (m-mult ker-ret6 h5-mat)))
	      (declare (type csparse f))
	      (setq h5-mat nil ker-ret6 nil) ;; release to GC
	      (format t "~&Computing SNF of f ...~&")
	      (let* ((snf5 (make-snf f t nil t t))
		     (h5 (- (m-num-cols ker6) (rank snf5))))
		(declare (type nnfixnum h5))
		(format t "~&H^5(..., Z) HAS RANK ~D~&" h5)
		(format t "~&f HAS TORSION ~S~&"
			(mapcar #'abs (torsion snf5)))
		(setq f nil) ;; release to GC
		(let ((cok-section-f (shh2::m-coker-section snf5)))
		  (declare (type csparse cok-section-f))
		  (setq snf5 nil) ;; release to GC
		  (let ((map-from-h5 (m-mult ker6 cok-section-f)))
		    (declare (type csparse map-from-h5))
		    (setq ker6 nil cok-section-f nil) ;; release to GC
		    (progn ;; debug progn clause
		      (assert (m-product-zerop h6-mat-copy map-from-h5)
			  () "Didn't get cocycles!")
		      (format t "~&Checked that they are 5-cocycles.~&"))
		    (print-entries map-from-h5 *eqco4n-output*))))))))
		    |#
      ;; Next line commented out 9/17/2007 in favor of perm-ech.
      ;; Commented out again 12/27/2007 in favor of coh-with-carryover.
      ;; (univ-coeff h6-mat h5-mat :n2 n6 :n1 n5 :n0 n4)
      ;; (coh-with-ech-im h6-mat h5-mat :n2 n6 :n1 n5 :n0 n4)
      (coh-with-carryover h6-mat h5-mat :n2 n6 :n1 n5 :n0 n4)
      )))

(defun univ-coeff (delta1 delta0 &key n2 n1 n0 (stream t))
  "Prints out a basis of cocycles for H^1 of the cochain complex of
free D-modules

  0 <---- D^n2 <--delta1-- D^n1 <--delta0-- D^n0

  =>      H^2              H^1

There are two ways to call the function.
[.] Provide delta1, delta0 as csparses, and provide the optional n
    arguments.  The function will compute the snf's of the deltas,
    which typically takes a lot of time and space.
[.] Provide the file-counter numbers (fc's) for pre-computed snf's
    of delta1 and delta0.  The function will get the snf's via
    make-snf-from-disk.  The optional n arguments are ignored.
The cocycles are printed to 'stream', which defaults to t (standard
output).  If 'stream' is nil, they are not printed.  Other messages
are always printed to standard output."
  (let ((snf1 nil)
	(snf0 nil)
	(field-p (sp-field-p (make-sp -1 0)))
	(z-quo-domain-p (or (sp-f_p-p (make-sp -1 0)) (sp-z-p (make-sp -1 0))))
	(rn (sp-ring-name (make-sp -1 0))))
    (declare (string rn))
    (etypecase delta1
      (integer
       (setq snf1 (make-snf-from-disk delta1 +make-sp+)
	     n2 (m-num-rows snf1)
	     n1 (m-num-cols snf1)))
      (csparse
       (assert (and (= (m-num-rows delta1) n2) (= (m-num-cols delta1) n1)) ()
	 "Dimension mismatch in the csparse delta1.")))
    (etypecase delta0
      (integer
       (setq snf0 (make-snf-from-disk delta0 +make-sp+)
	     n0 (m-num-cols snf0))
       (assert (= (m-num-rows snf0) n1) () "Inner dimension mismatch."))
      (csparse
       (assert (and (= (m-num-rows delta0) n1) (= (m-num-cols delta0) n0)) ()
	 "Dimension mismatch in the csparse delta1.")))
    (format t "~&Finding H^* of the cochain complex~&  0 <---- ~A^~D <--delta1-- ~A^~D <--delta0-- ~A^~D" rn n2 rn n1 rn n0)
    (unless snf1
      (format t "~&Computing SNF of delta1, ~A ...~&" (time-stamp))
      (setq snf1 (make-snf delta1 nil t t t)))
    (let* ((rank1 (rank snf1))
	   (dimker1 (- n1 rank1)))
      (declare (type nnfixnum rank1 dimker1))
      (if field-p
	  (format t "~&H^2(..., ~A) HAS DIMENSION ~D~&" rn (- n2 rank1))
	(progn
	  (format t "~&H^2(..., ~A) HAS RANK ~D~&" rn (- n2 rank1))
	  (format t "~&H^2(..., ~A) HAS TORSION ~S~&"
		  rn (mapcar #'sp-print-value (mapcar #'sp-pretty-associate (torsion snf1))))))
      (unless snf0
	(format t "~&Computing SNF of delta0, ~A ...~&" (time-stamp))
	(setq snf0 (make-snf delta0 t nil t t)))
      (let* ((ones0 (num-units snf0))
	     (rank0 (rank snf0))
	     (h-1 (- dimker1 rank0)))
	(declare (type nnfixnum ones0 rank0))
	(if field-p
	    (format t "~&H^1(..., ~A) HAS DIMENSION ~D~&" rn h-1)
	  (progn
	    (format t "~&H^1(..., ~A) HAS RANK ~D~&" rn h-1)
	    (format t "~&delta0 HAS NON-UNIT ELEMENTARY DIVISORS ~S ~&"
		    (mapcar #'sp-print-value (mapcar #'sp-pretty-associate (torsion snf0))))))
	;; The csparse K = kk will have size n1 by something <= dimker1.
	(let (kk kk-cols ;; here for historical reasons
	      (kk-vec (make-array 0 :adjustable t :fill-pointer t))
	      (kk-vec-last-len -1))
	  (declare (vector kk-vec) (fixnum kk-vec-last-len))
	  (let ((q1-inv-list '()) ;; (mapcar #'m-inverse [q's, l-to-r order])
		(p0-inv-list '())
		(one-col (if z-quo-domain-p ;; see oo in do-minor-trick
			     (make-array n1 :initial-element 0)
			   (make-csparse-zero n1 1)))) ;; same for p's
	    (do-snf-q-rev (q snf1)
	      (push (m-inverse q) q1-inv-list))
	    (do-snf-p-rev (p snf0)
	      (push (m-inverse p) p0-inv-list))
	    (format t "~&Computing K = ker(delta1) with up to ~D column~:P, one at a time.~&" dimker1)
	    (format t "~&For each, we'll multiply by ~D elementary matrices~&"
		    (+ (length q1-inv-list) (length p0-inv-list)))
	    (format t "~&and store up to ~D non-zero~:P.~&" (- n1 ones0))
	    (dotimes-f (j dimker1)
	      (when (or (let* ((kk-vec-len (length kk-vec))
			       (changed (/= kk-vec-len kk-vec-last-len)))
			  (declare (type nnfixnum kk-vec-len))
			  (when changed
			    (setq kk-vec-last-len kk-vec-len))
			  changed)
			(zerop (rem j 100)))
		(format t "~&   Span of column ~D and ~D other~:P ~A~&" j (length kk-vec) (time-stamp)))
	      (cond (z-quo-domain-p
		     (fill one-col 0)
		     (setf (aref one-col (+ rank1 j)) 1))
		    (t
		     (setf (shh2::csparse-cols one-col) '())
		     (shh2::reset-markowitz one-col)
		     (csparse-set one-col (make-sp (+ rank1 j) 1) 0)))
	      ;; one-col is a singleton-column matrix.  It is in coords
	      ;; of the right side of snf1's d.  Now change it to coords
	      ;; on the right side of snf1, viz. the left side of snf0.
	      (dolist (q q1-inv-list)
		(if z-quo-domain-p
		    (shh2::elem-times-vector q one-col)
		  (m-mult q one-col)))
	      ;; Further, change it to coords on the left side of snf0's d.
	      (dolist (p p0-inv-list)
		(if z-quo-domain-p
		    (shh2::elem-times-vector p one-col)
		  (m-mult p one-col)))
	      ;; Mod out the coords where snf0's d has 1's.  That is,
	      ;; cut off all rows i < ones0.
	      (unless z-quo-domain-p
		(with-splicer (svref (shh2::csparse-cols one-col) 0)
		  (till (or (splicer-endp) (>= (sp-i (splicer-read)) ones0))
		    (splicer-delete))))
	      (let ((next-v (if z-quo-domain-p
				(do ((i (1- n1) (1- i))
				     (v '()))
				    ((< i ones0) v)
				  (declare (fixnum i) (type sparse-v v))
				  (let ((val (svref one-col i)))
				    (declare (integer val))
				    (unless (zerop val)
				      (push (make-sp i val) v))))
			      (svref (shh2::csparse-cols one-col) 0))))
		(declare (type sparse-v next-v))
		(when next-v
		  (vector-push-extend next-v kk-vec)))
	      (hnf kk-vec)
	      ;; Can do something similiar to the next trick in the Z
	      ;; case.  When the number of cycle generators is large
	      ;; enough (h-1? that plus number of torsion
	      ;; generators?), check whether the hnf is saturated,
	      ;; which I think means that the pivot of each column
	      ;; (bottom, for the method hnf) is a unit.  I don't
	      ;; think the hnf has to get saturated, whether or not
	      ;; the final cohomology has torsion, but it might.  Even
	      ;; more: we already know the finite set of primes which
	      ;; might appear in the torsion, and saturated can mean
	      ;; relatively prime to that set.
	      (when (and field-p (= (length kk-vec) h-1))
		(format t "~&Got a vector space basis of ~D cycle~:P at column ~D.~&" h-1 j)
		(return))))
	  (when field-p
	    (assert (= (length kk-vec) h-1) ()
	      "At end of hnf, got /= ~D cycle~:P." h-1))
	  (setq kk-cols (copy-seq kk-vec)
		kk (shh2::reset-markowitz
		    (shh2::make-csparse
		     :m n1 :n (length kk-cols) :cols kk-cols
		     :rlen (make-array n1 :initial-element -1)
		     :clen (make-array (length kk-cols) :initial-element -1))))
	  ;; From now on, kk is fixed.  It's a basis of cocycles
	  ;; generating our cohomology group with rn coefficients.
	  ;; <P> Now, print out the torsion strip.  This is the block of
	  ;; kk fitting in rows ones0 <= i < rank0, and using only the
	  ;; columns that fit entirely in this range of rows.
	  (when field-p
	    (assert (= ones0 rank0) () "ones0 < rank0 over a field?"))
	  (let ((num-torsion-cols 0))
	    (block num-torsion-cols-loop
	      (dotimes-f (j (m-num-cols kk))
		(dolist (e (svref kk-cols j))
		  (when (>= (sp-i e) rank0)
		    (return-from num-torsion-cols-loop)))
		(incf num-torsion-cols)))
	    (when field-p
	      (assert (zerop num-torsion-cols) ()
		"num-torsion-cols > 0 over a field?"))
	    (let ((torsion-strip (make-dense-matrix-z (- rank0 ones0) num-torsion-cols))
		  (modulus-strip (make-dense-matrix-z (- rank0 ones0) (- rank0 ones0))))
	      (dotimes-f (j num-torsion-cols)
		(dolist (e (svref kk-cols j))
		  (setf (aref torsion-strip (- (sp-i e) ones0) j)
		    (shh2::sp-integer-value e))))
	      (dotimes-f (j (- rank0 ones0))
	        (setf (aref modulus-strip j j)
		  (shh2::sp-integer-value (csparse-get (slot-value snf0 'shh2::d) (+ j ones0) (+ j ones0)))))
	      (unless field-p
		(format t "~&Torsion in H^1 is the quotient of")
		(format t "~&the ~A-module spanned by the columns of" rn)
		(format t "~&~A" torsion-strip)
		(format t "~&by the ~A-module spanned by the columns of" rn)
		(format t "~&~A" modulus-strip)))
	    ;; Find cocycles.
	    (if field-p
		(format t "~&Computing ~D cocycles ~A ..." (m-num-cols kk) (time-stamp))
	      (format t "~&Computing cocycles (first ~D torsion, remaining ~D non-torsion), ~A ..." num-torsion-cols (- (m-num-cols kk) num-torsion-cols) (time-stamp)))
	    (let ((kkz (csparse-copy kk)))
	      (do-snf-p-rev (p snf0)
		(m-mult p kkz))
	      (let ((kkz1 (csparse-copy kkz)))
		(do-snf-q-rev (q snf1)
		  (m-mult q kkz1))
		;; A column of kkz is a cocycle iff the corresponding
		;; column of kkz1 has no entry of index < rank1.
		(shh2::with-csparse-slots ((kkz1-n shh2::n) (kkz1-cols shh2::cols)) kkz1
		  (dotimes-f (j kkz1-n)
		    (unless (or (endp (svref kkz1-cols j))
				(>= (sp-i (first (svref kkz1-cols j))) rank1))
		      (error "Generator ~D over ~A is not a cocycle." j rn)))))
	      (when stream
		(shh2::with-csparse-slots ((kkz-n shh2::n) (kkz-cols shh2::cols)) kkz
		  (dotimes-f (j kkz-n)
		    (format stream "~&COCYCLE OVER ~A" rn)
		    (when (< j num-torsion-cols)
		      (format stream " (TORSION)"))
		    (shh2::v-print-line-by-line t (svref kkz-cols j) n1))))))
	  (unless (endp (torsion snf1))
	    (let ((more-tor (format nil "THERE MAY BE **MORE TORSION** AT PRIMES DIVIDING ~A.  Port over that code." (sp-print-value (sp-pretty-associate (first (last (torsion snf1))))))))
	      (format t "~&~A~&" more-tor)
	      (when (and stream (not (eq stream t)))
		(format stream "~&~A~&" more-tor))))
	  (awhile (progn
		    (format t "~&Enter a filename with a cocycle to be~&resolved against this basis [or 'loop', or 'nil' to quit]? ")
		    (read))
	    (if (equalp (format nil "~A" it) "loop")
		(let ((kkn (m-num-cols kk)))
		  (format t "~&Enter a filename stem like '[dir]\\cy79_'.~&I'll run resolve-cocycle-from-file on stemNN~&for NN from 1 through ~D, then stemNN.t.2.1 for~&these NN, then stemNN.t.2.2, then stemNN.t.2.3 for~&these NN, then 3.1, 3.2, 3.3, 5.1, 5.2, and 5.3.~&? " kkn)
		  (let ((stem (format nil "~A" (read))))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.2.1" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.2.2" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.2.3" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.3.1" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.3.2" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.3.3" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.5.1" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.5.2" stem i) snf1 snf0 kk))
		    (do ((i 1 (1+ i)))
			((> i kkn))
		      (resolve-cocycle-from-file (format nil "~A~D.t.5.3" stem i) snf1 snf0 kk))))
	      (resolve-cocycle-from-file (format nil "~A" it) snf1 snf0 kk))))))))

(defun resolve-cocycle-from-file (filename snf1 snf0 kk)
  (declare (string filename) (type snf snf1 snf0) (type csparse kk))
  (handler-bind ((error
		  #'(lambda (c)
		      (format t "~&~A~&Skipping this file.~&" c)
		      (return-from resolve-cocycle-from-file))))
    (let ((n1 (m-num-cols snf1))
	  (ones0 (num-units snf0)))
      (declare (type nnfixnum n1 ones0))
      (assert (= n1 (m-num-rows snf0)) () "Dimension mismatch!")
      (let ((oo (make-array n1 :initial-element 0)))
	(with-open-file (s filename :direction :input)
	  (let ((j 0))
	    (declare (type nnfixnum j))
	    (awhile (read-line s nil)
	      (let ((e (parse-z-one-half it j)))
		(unless (sp-zerop e)
		  (setf (svref oo j) (shh2::sp-integer-lift e))))
	      (incf j))
	    (assert (= j n1) ()
	      "Cocycle has length ~D, but should have length ~D." j n1)))
	(do-snf-p (p snf0)
	  (shh2::elem-times-vector (m-inverse p) oo))
	(let ((rhs (make-csparse-zero n1 1)))
	  (do ((j (1- n1) (1- j)))
	      ((< j ones0))
	    (unless (zerop (svref oo j))
	      (let ((e (make-sp j (svref oo j))))
		(unless (sp-zerop e)
		  (csparse-set rhs e 0)))))
	  (setq oo nil) ;; gc-help
	  (let ((kk-with-one-dep (csparse-concat-left-right kk rhs))
		(*show-stats* nil)
		(*show-csw* nil))
	    (let ((one-dep-snf (make-snf kk-with-one-dep nil t t nil)))
	      (let ((one-dep-ker (shh2::m-ker one-dep-snf +make-sp+)))
		(let ((odk-last-i (1- (m-num-rows one-dep-ker))))
		  (assert (= (m-num-cols one-dep-ker) 1) ()
		    "Didn't get one dependency, but ~D." (m-num-cols one-dep-ker))
		  (assert (= odk-last-i (m-num-cols kk)) ()
		    "Programmer got odk-last-i wrong.")
		  (multiple-value-bind (pr u) (sp-pretty-associate (csparse-get one-dep-ker odk-last-i 0))
		    (assert (not (sp-zerop pr)) ()
		      "Got one dependency, but not involving rhs.")
		    (when (sp-field-p pr)
		      (assert (and (sp-onep pr) (equal u (csparse-get one-dep-ker odk-last-i 0))) ()
			"Bug in sp-pretty-associate?"))
		    (let ((uu (sp-divided-by (make-sp (sp-i u) -1) u)))
		      (map-into (svref (shh2::csparse-cols one-dep-ker) 0)
				#'(lambda (e) (sp-mult e uu))
				(svref (shh2::csparse-cols one-dep-ker) 0))))
		  (when (sp-field-p (csparse-get one-dep-ker odk-last-i 0))
		    (assert (sp-neg-one-p (csparse-get one-dep-ker odk-last-i 0)) ()
		      "Last entry is not -1."))
		  (format t "~&Dotting (basis basis ... basis input) with~&the following gives zero:~&~A~&" one-dep-ker))))))))))

(defun parse-z-one-half (line index)
  "If line holds an integer, use this value.
If line holds 'xxx d yyy', use the value xxx / 2^yyy.
In both cases, return the sparse-elt with the indicated value
and the given index.  The name means we're working over Z[1/2]."
  (let ((d-loc (position #\d line :test #'char-equal)))
    (let ((x (parse-integer line :end d-loc))
	  (y (if d-loc (parse-integer line :start (1+ d-loc)) 0)))
      (let ((ans (make-sp index x)))
	(if (zerop y)
	    ans
	  (let ((two-y (make-sp -1 (expt 2 y))))
	    (assert (and (not (sp-zerop two-y)) (sp-divides two-y ans)) ()
	      "Can't divide by ~D in ~A." (expt 2 y) (sp-ring-name ans))
	    (sp-divided-by ans two-y)))))))    

(defun dumpcynn (in-name out-stem change-prefix end-prefix)
  "Reads the file in-name from the cwd.  Writes it out line by line to
files whose names are obtained by appending 1, 2, ..., to out-stem.
We start a new file whenever a line begins with change-prefix.  The
change lines are not written out, and lines before the first change
line are not written out.  We stop reading and writing the first time
a line begins with end-prefix."
  (labels ((starts-with (text prefix prefix-len)
	     (and (<= prefix-len (length text))
		  (string= prefix text :end2 prefix-len))))
    (let ((i 0)
	  (clen (length change-prefix))
	  (elen (length end-prefix))
	  (so nil))
      (with-open-file (si in-name)
	(do ((line (read-line si nil) (read-line si nil)))
	    ((null line)
	     (when so (close so)))
	  (cond ((starts-with line change-prefix clen)
		 (when so (close so))
		 (incf i)
		 (setq so (open (format nil "~A~D" out-stem i)
				:direction :output :if-exists :supersede)))
		((starts-with line end-prefix elen)
		 (when so (close so))
		 (return-from dumpcynn))
		(so
		 (format so "~&~A~&" line))))))))

;;; - - - - - - - - - -

(defun coh-with-carryover (delta1 delta0 &key n2 n1 n0)
  "Prints out a basis of cocycles for H^1 of the cochain complex of
F-vector spaces

  0 <---- F^n2 <--delta1-- F^n1 <--delta0-- F^n0

  =>      H^2              H^1

or finds coordinates of given cocycles with respect to this basis.
Currently F = Z/pZ.  There are two ways to call the function.
[.] Provide delta1, delta0 as csparses, and provide the optional n
    arguments.  The function will compute the snf P1 D1 Q1 of delta1.
    The matrix Q1 delta0 will have rank1 rows of zeroes on top,
    where rank1 is the rank of delta1.  Let eta be Q1 delta0 with
    these rows of zeroes chopped off.  The function next computes the
    snf P0 D0 Q0 of eta, a job which typically takes a lot of time and
    space.
[.] Provide the file-counter numbers (fc's) for pre-computed snf's
    of delta1 and eta.  The function will get the snf's via
    make-snf-from-disk.  The optional n arguments are ignored.
The results are printed to standard output."
  (let ((snf1 nil) ;; snf of delta1
	(snf-eta nil) ;; snf of eta
	(rn (sp-ring-name (make-sp -1 0))))
    (declare (string rn))
    (assert (sp-f_p-p (make-sp -1 0)) ()
      "This experimental coh-with-carryover code is currently only for F_p.")
    (etypecase delta1
      (integer
       (setq snf1 (make-snf-from-disk delta1 +make-sp+)
	     n2 (m-num-rows snf1)
	     n1 (m-num-cols snf1)))
      (csparse
       (assert (and (= (m-num-rows delta1) n2) (= (m-num-cols delta1) n1)) ()
	 "Dimension mismatch in the csparse delta1.")))
    (etypecase delta0
      (integer
       (setq snf-eta (make-snf-from-disk delta0 +make-sp+)
	     n0 (m-num-cols snf-eta)))
      (csparse
       (assert (and (= (m-num-rows delta0) n1) (= (m-num-cols delta0) n0)) ()
	 "Dimension mismatch in the csparse delta0.")))
    (format t "~&Finding H^* of the cochain complex~&  0 <---- ~A^~D <--delta1-- ~A^~D <--delta0-- ~A^~D" rn n2 rn n1 rn n0)
    (unless snf1
      (format t "~&Computing SNF of delta1, ~A ...~&" (time-stamp))
      (setq snf1 (make-snf delta1 nil t t t)))
    (let* ((rank1 (rank snf1))
	   (dimker1 (- n1 rank1))
	   (betti2 (- n2 rank1)))
      (declare (fixnum rank1 dimker1 betti2))
      (assert (>= betti2 0) ()
	"Negative Betti number h2.")
      (format t "~&H^2(..., ~A) HAS DIMENSION ~D~&" rn betti2)
      (if snf-eta
	  (assert (= dimker1 (m-num-rows snf-eta)) ()
	    "Inner dimension mismatch.")
	(let ((eta-tr (m-transpose delta0)) ;; n0 by n1
	      (eta (make-csparse-zero dimker1 n0)))
	  (format t "~&Converting delta0 to eta, ~A ...~&" (time-stamp))
	  (do-snf-q-rev (q snf1)
	    (m-mult eta-tr (m-transpose q)))
	  (dotimes-f (j n1)
	    (let ((v (svref (shh2::csparse-cols eta-tr) j)))
	      (if (< j rank1)
		  (assert (v-zerop v) ()
		    "Eta does not have the expected strip of 0's at the top.")
		(dolist (e v)
		  (push (copy-sp e (- j rank1))
			(svref (shh2::csparse-cols eta) (sp-i e)))))))
	  (dotimes-f (j n0)
	    (setf (svref (shh2::csparse-cols eta) j)
	      (nreverse (svref (shh2::csparse-cols eta) j))))
	  (shh2::reset-markowitz eta)
	  (setq eta-tr nil delta0 nil) ;; gc-help
	  (format t "~&Computing SNF of eta, ~A ...~&" (time-stamp))
	  (setq snf-eta (make-snf eta t nil t t))))
      (let* ((rank0 (rank snf-eta))
	     ;; (rr (+ rank1 rank0)) ;; TAKE OUT TAKE OUT
	     (betti1 (- dimker1 rank0)))
	(declare (fixnum rank0 betti1))
	(assert (>= betti1 0) ()
	  "Negative Betti number h1.")
	(format t "~&H^1(..., ~A) HAS DIMENSION ~D~&" rn betti1)
	;; In coords on the RHS of P0, a basis of H^1 is the i-th
	;; coordinate vectors for i in [rank0, dimker1).  betti1 is
	;; the number of these vectors.
	(format t "~&Print the std basis of cocycles [enter nil for no]? ")
	(when (read)
	  (let ((kk-tr (make-csparse-zero betti1 dimker1))
		(kk-tr-wide (make-csparse-zero betti1 n1)))
	    (dotimes-f (j betti1)
	      (csparse-set kk-tr (make-sp j 1) (+ rank0 j)))
	    (do-snf-p-rev (p snf-eta)
	      (m-mult kk-tr (m-transpose p)))
	    (dotimes-f (j dimker1)
	      (setf (svref (shh2::csparse-cols kk-tr-wide) (+ j rank1))
		(svref (shh2::csparse-cols kk-tr) j))
	      (setf (svref (shh2::csparse-cols kk-tr) j)
		'()))
	    (do-snf-q (q snf1)
	      (m-mult kk-tr-wide (m-inverse-transpose q)))
	    (let ((kk (m-transpose kk-tr-wide)))
	      (setq kk-tr nil kk-tr-wide nil) ;; gc-help
	      (dotimes-f (j betti1)
		(format t "~&COCYCLE OVER ~A" rn)
		(shh2::v-print-line-by-line t (svref (shh2::csparse-cols kk) j) n1)))))
	(labels ((resolve-cocycle (filename)
		   (handler-bind ((error
				   #'(lambda (c)
				       (format t "~&~A~&Skipping this file.~&" c)
				       (return-from resolve-cocycle))))
		     (let ((oo (make-csparse-zero n1 1)))
		       (macrolet ((oc () '(svref (shh2::csparse-cols oo) 0)))
		         (with-open-file (s filename)
			   (let ((j 0))
			     (declare (type nnfixnum j))
			     (awhile (read-line s nil)
			       (let ((e (parse-z-one-half it j)))
				 (unless (sp-zerop e)
				   (push e (oc))))
			       (incf j))
			     (assert (= j n1) ()
			       "Cocycle has length ~D, but should have length ~D." j n1)))
			 (setf (oc) (nreverse (oc)))
			 ;; (shh2::reset-markowitz oo)
			 (do-snf-q-rev (q snf1)
			   (m-mult q oo))
			 (assert (or (v-zerop (oc)) (<= rank1 (sp-i (first (oc))))) ()
			   "Not a cocycle.")
			 (setf (oc)
			   (mapcar #'(lambda (e)
				       (copy-sp e (- (sp-i e) rank1)))
				   (oc)))
			 ;; From now on, pretend oo is dimker1 by 1 instead
			 ;; of n1 by 1.
			 (do-snf-p (p snf-eta)
			   (m-mult (m-inverse p) oo))
			 (till (or (v-zerop (oc))
				   (>= (sp-i (first (oc))) rank0))
			   (pop (oc)))
			 ;; (shh2::reset-markowitz oo)
			 (format t "~&Resolution w.r.t. std basis:")
			 (do ((i rank0 (1+ i)))
			     ((= i dimker1))
			   (declare (type nnfixnum i))
			   (format t "~&")
			   (let ((e (v-get (oc) i)))
			     (if e
				 (sp-print-value e t)
			       (format t "0")))))))))
	  (awhile (progn
		    (format t "~&Enter a filename with a cocycle to be~&resolved against this basis [or 'basis', 'loop',~&or 'nil' to quit]? ")
		    (read))
	    (cond ((equalp (format nil "~A" it) "basis")
		   (format t "~&Enter a filename stem like '[dir]\\cy79_'.~&I'll run resolve-cocycle on stemNN~&for NN from 1 through ~D.  ? " betti1)
		   (let ((stem (format nil "~A" (read))))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D" stem i)))))
		  ((equalp (format nil "~A" it) "loop")
		   (format t "~&Enter a filename stem like '[dir]\\cy79_'.~&I'll run resolve-cocycle on stemNN~&for NN from 1 through ~D, then stemNN.t.2.1 for~&these NN, then stemNN.t.2.2, then stemNN.t.2.3 for~&these NN, then 3.1, 3.2, 3.3, 5.1, 5.2, 5.3.  ? " betti1)
		   (let ((stem (format nil "~A" (read))))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.2.1" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.2.2" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.2.3" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.3.1" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.3.2" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.3.3" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.5.1" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.5.2" stem i)))
		     (do ((i 1 (1+ i)))
			 ((> i betti1))
		       (resolve-cocycle (format nil "~A~D.t.5.3" stem i)))))
		  (t
		   ;; Here 'it' is the filename of a cocycle to resolve.
		   (resolve-cocycle (format nil "~A" it))))))))))

;;; - - - - - - - - - -

(defun coh-with-ech-im (delta1 delta0 &key n2 n1 n0)
  "Prints out a basis of cocycles for H^1 of the cochain complex of
F-vector spaces

  0 <---- F^n2 <--delta1-- F^n1 <--delta0-- F^n0

  =>      H^2              H^1

or finds coordinates of given cocycles with respect to this basis.
Currently F = Z/pZ.  There are two ways to call the function.
[.] Provide delta1, delta0 as csparses, and provide the optional n
    arguments.  The function will compute the snf P1 D1 Q1 of delta1.
    Letting eta = Q1 delta0, it will compute the perm-ech P0 E0 of eta.
[.] Provide the file-counter numbers (fc's) for a pre-computed snf
    of delta1 and a pre-computed perm-echelon form of eta.  The
    optional n arguments are ignored.
The results are printed to standard output."
  (let ((snf1 nil)
	(pe0 nil)
	(rn (sp-ring-name (make-sp -1 0))))
    (declare (string rn))
    (assert (sp-f_p-p (make-sp -1 0)) ()
      "This experimental perm-echelon code is currently only for F_p.")
    (etypecase delta1
      (integer
       (setq snf1 (make-snf-from-disk delta1 +make-sp+)
	     n2 (m-num-rows snf1)
	     n1 (m-num-cols snf1)))
      (csparse
       (assert (and (= (m-num-rows delta1) n2) (= (m-num-cols delta1) n1)) ()
	 "Dimension mismatch in the csparse delta1.")))
    (etypecase delta0
      (integer
       (setq pe0 (make-perm-ech-from-disk delta0)
	     n0 (m-num-cols pe0))
       (assert (= n1 (m-num-rows pe0)) () "Inner dimension mismatch."))
      (csparse
       (assert (and (= (m-num-rows delta0) n1) (= (m-num-cols delta0) n0)) ()
	 "Dimension mismatch in the csparse delta0.")))
    (format t "~&Finding H^* of the cochain complex~&  0 <---- ~A^~D <--delta1-- ~A^~D <--delta0-- ~A^~D" rn n2 rn n1 rn n0)
    (unless snf1
      (format t "~&Computing SNF of delta1, ~A ...~&" (time-stamp))
      (setq snf1 (make-snf delta1 nil t t t)))
    (let* ((rank1 (rank snf1))
	   (dimker1 (- n1 rank1))
	   (betti2 (- n2 rank1)))
      (declare (fixnum rank1 dimker1 betti2))
      (assert (>= betti2 0) ()
	"Negative Betti number h2.")
      (format t "~&H^2(..., ~A) HAS DIMENSION ~D~&" rn betti2)
      (unless pe0
	(let ((eta-tr (m-transpose delta0))
	      (eta nil))
	  (format t "~&Converting delta0 to eta, ~A ...~&" (time-stamp))
	  (do-snf-q-rev (q snf1)
	    (m-mult eta-tr (m-transpose q)))
	  (setq eta (m-transpose eta-tr)
		eta-tr nil delta0 nil) ;; gc-help
	  (assert (every #'(lambda (col)
			     (or (v-zerop col) (<= rank1 (sp-i (first col)))))
			 (shh2::csparse-cols eta)) ()
	    "Eta does not have the expected strip of zeroes at the top.")
	  (format t "~&Computing perm-echelon form of eta, ~A ...~&" (time-stamp))
	  (setq pe0 (make-perm-ech-from-csparse eta))))
      (let* ((rank0 (rank pe0))
	     (betti1 (- dimker1 rank0))
	     (P0 (shh2::perm-ech-P pe0))
	     (basis-inds (make-array betti1 :adjustable t :fill-pointer 0)))
	(declare (fixnum rank0 betti1) (type perm P0))
	(assert (>= betti1 0) ()
	  "Negative Betti number h1.")
	(format t "~&H^1(..., ~A) HAS DIMENSION ~D~&" rn betti1)
	(let ((h (make-hash-table :size dimker1)))
	  (declare (hash-table h))
	  (do ((i-lhs-P0 rank1 (+ i-lhs-P0 1)))
	      ((= i-lhs-P0 n1))
	    (declare (type nnfixnum i-lhs-P0))
	    (puthash i-lhs-P0 t h))
	  (dolist (i-rhs-P0 (shh2::perm-ech-piv-i-list pe0))
	    (declare (type nnfixnum i-rhs-P0))
	    (remhash (m-mult P0 i-rhs-P0) h))
	  (assert (= (hash-table-count h) betti1) ()
	    "Error finding the basis indices.")
	  (maphash #'(lambda (i-lhs-P0 value)
		       (declare (ignore value))
		       (vector-push-extend i-lhs-P0 basis-inds))
		   h))
	(shh2::sortf basis-inds #'<)
	(assert (= (length basis-inds) betti1) ()
	  "Error (push-extend) finding the basis indices.")
	(format t "~&Print the std basis of cocycles [enter nil for no]? ")
	(when (read)
	  (let ((kk (make-csparse-zero n1 betti1)))
	    (dotimes-f (j betti1)
	      (csparse-set kk (make-sp (aref basis-inds j) 1) j))
	    (do-snf-q (q snf1)
	      (m-mult (m-inverse q) kk))
	    (dotimes-f (j betti1)
	      (format t "~&COCYCLE OVER ~A" rn)
	      (shh2::v-print-line-by-line t (svref (shh2::csparse-cols kk) j) n1))))
	(labels ((resolve-cocycle (filename)
		   (handler-bind ((error
				   #'(lambda (c)
				       (format t "~&~A~&Skipping this file.~&" c)
				       (return-from resolve-cocycle))))
		     (let ((oo (make-csparse-zero n1 1)))
		       (macrolet ((oc () '(svref (shh2::csparse-cols oo) 0)))
		         (with-open-file (s filename)
			   (let ((j 0))
			     (declare (type nnfixnum j))
			     (awhile (read-line s nil)
			       (let ((e (parse-z-one-half it j)))
				 (unless (sp-zerop e)
				   (push e (oc))))
			       (incf j))
			     (assert (= j n1) ()
			       "Cocycle has length ~D, but should have length ~D." j n1)))
			 (setf (oc) (nreverse (oc)))
			 ;; (shh2::reset-markowitz oo)
			 (do-snf-q-rev (q snf1)
			   (m-mult q oo))
			 (assert (or (v-zerop (oc)) (<= rank1 (sp-i (first (oc))))) ()
			   "Not a cocycle.")
			 (m-mult (m-inverse P0) oo)
			 (do-perm-ech-cols (col pe0)
			   (assert col ()
			     "eche file has empty column.")
			   (assert (sp-onep (first col)) ()
			     "eche file has column not starting with 1.")
			   (let* ((i (sp-i (first col)))
				  (e (v-get (oc) i)))
			     (when e
			       (setf (oc) (v-alter (oc) (sp-negate e) col))
			       ;; (shh2::reset-markowitz oo)
			       )))
			 (m-mult P0 oo)
			 (assert (every #'(lambda (e)
					    (>= (shh2::bsearch-integer (sp-i e) basis-inds) 0))
					(oc)) ()
			   "Resolved cocycle not in expected range of ~D row~:P on LHS eta." betti1)
			 (format t "~&Resolution w.r.t. std basis:")
			 (map nil #'(lambda (i)
				      (declare (type nnfixnum i))
				      (format t "~&")
				      (let ((e (v-get (oc) i)))
					(if e
					    (sp-print-value e t)
					  (format t "0"))))
			      basis-inds))))))
	  (awhile (progn
		    (format t "~&Enter a filename with a cocycle to be~&resolved against this basis [or 'loop', or 'nil' to quit]? ")
		    (read))
	    (if (equalp (format nil "~A" it) "loop")
		(progn
		  (format t "~&Enter a filename stem like '[dir]\\cy79_'.~&I'll run resolve-cocycle on stemNN~&for NN from 1 through ~D, then stemNN.t.2.1 for~&these NN, then stemNN.t.2.2, then stemNN.t.2.3 for~&these NN.  ? " betti1)
		  (let ((stem (format nil "~A" (read))))
		    (do ((i 1 (1+ i)))
			((> i betti1))
		      (resolve-cocycle (format nil "~A~D" stem i)))
		    (do ((i 1 (1+ i)))
			((> i betti1))
		      (resolve-cocycle (format nil "~A~D.t.2.1" stem i)))
		    (do ((i 1 (1+ i)))
			((> i betti1))
		      (resolve-cocycle (format nil "~A~D.t.2.2" stem i)))
		    (do ((i 1 (1+ i)))
			((> i betti1))
		      (resolve-cocycle (format nil "~A~D.t.2.3" stem i)))))
	      ;; Here 'it' is the filename of a cocycle to resolve.
	      (resolve-cocycle (format nil "~A" it)))))))))

;;; ------------------------------------------------------------

;;; Functions for creating orbits.

(defvar printing-table)

(defun parse (gp pt-to-code pt-to-orep ans)
  ;; gp  is a list of pairs ((col col col col) . sign) .  Output is a
  ;; list of CPT rep'ves of right  gp -orbits in P^3 --more precisely, the
  ;; orbits in which no pt gets both +1 and -1.  If pt-to-code is non-nil,
  ;; it is an array, where all points of the current orbit will be
  ;; made keys with value equal to the current value of kount.  Kount
  ;; is incremented after each use.  ans should initially be '() .
  (declare (list gp ans))
  (loop
    (let ((next-x (next-in-cpt-set)))
      (if (null next-x)
	  (return-from parse (nreverse ans)) ;; done.  The nreverse matters!
	(let* ((x (the cpt next-x)) ;; the rep've of the next orbit
	       (y (make-orbit gp x)) ;; the orbit, with repetitions
	       (z (winnow-orbit y)))
	  (declare (type cpt x) (list y z))
	  ;; Whether or not the orbit is winnowed, (svref pt-to-orep a)
	  ;; will return x for all CPTs a in this orbit.
	  (when pt-to-orep
	    (dolist (pair y) ;; pair = (a . s)
	      (setf (svref (the simple-vector pt-to-orep) (the cpt (car pair)))
		x)))
	  ;; z is the orbit (... (cpt . sign) ...) , unless some pt
	  ;; occurred with both signs, in which case z is nil.
	  (when (and pt-to-code z)
	    (dolist (a z) ;; a = (pt . sign)
	      (setf (svref (the simple-vector pt-to-code) (the cpt (car a)))
		kount))
	    (incf kount))
	  ;; The next when clause is used for printing.
	  (when (and *print-orbits* z)
	    (let ((lyst '()))
	      (maphash #'(lambda (k v)
			   ;; printing-table should point to a hash table
			   ;; whose keys are the PPTs from this orbit, and
			   ;; whose values are the [most recent] elt of gp
			   ;; that produced it
			   (cond (*print-projective-points*
				  (push (list (ppt-to-cpt k) (cdr v) (car v)) lyst))
				 (t
				  (push (list k (cdr v) (car v)) lyst))))
		       printing-table)
	      (push (sort lyst #'(lambda (a b) (>= (the fixnum (cadr a))
						   (the fixnum (cadr b)))))
		    whole-orbit-list)))
	  (dolist (pair y) ;; pair = (a . s)
	    (setf (sbit *cpt-set* (the cpt (car pair))) 0))
	  (when z
	    (push x ans)))))))

(defun make-orbit (gp x)
  ;; gp  is as in parse.  x is a CPT in P^3.  Output is the list of pairs
  ;; (cpt . s) for all g in  gp , where cpt = x*g and  s  is the sign of
  ;; g.
  (declare (type cpt x))
  (when *print-orbits*
    (setq printing-table (make-hash-table :test #'equal)))
  (let ((x-ppt (cpt-to-ppt x))
;            )
;    (mapcar #'(lambda (g) (parse-aux g x-ppt)) gp)))
	(ans '()))
    (do ((i 0 (1+ i))
	 (glist gp (cdr glist)))
	((null glist)
	 (nreverse ans))
      (declare (fixnum i))
      (push (parse-aux-with-printing (car glist) x-ppt i) ans))))

(defvar *print-full-stab-matrices* nil)

(defun parse-aux-with-printing (gp-elt pt gp-elt-num)
  ;; gp-elt is a dotted pair ((col col col col) . sign) .  Output is
  ;; the dotted pair ( [ pt * matrix , projectively-niced ] . sign).
  ;; The input pt is a PPT, but the point in the output is a CPT.
  ;; 5/9/99: gp-elt-num is the position in list of the stabilizer
  ;; matrix used.
  (let ((output-ppt (proj-nice
		     (mapcar #'(lambda (col) (the fixnum (list-dot pt col)))
			     (car gp-elt)))))
    (when *print-orbits*
      (setf (gethash output-ppt printing-table)
	(if *print-full-stab-matrices*
	    gp-elt
	  (cons gp-elt-num (cdr gp-elt)))))
    (cons
     (ppt-to-cpt output-ppt)
     (the fixnum (cdr gp-elt)))))

(defun parse-aux (gp-elt pt)
  ;; gp-elt is a dotted pair ((col col col col) . sign) .  Output is
  ;; the dotted pair ( [ pt * matrix , projectively-niced ] . sign).
  ;; The input pt is a PPT, but the point in the output is a CPT.
  (let ((output-ppt (proj-nice
		     (mapcar #'(lambda (col) (the fixnum (list-dot pt col)))
			     (car gp-elt)))))
    (cons
     (ppt-to-cpt output-ppt)
     (the fixnum (cdr gp-elt)))))

(defun list-dot (a b)
  ;; a and b are lists rep'g vectors, which are taken for granted to
  ;; be of the same length.  This finds their dot product.  The
  ;; declarations assume a is a PPT and the entries in b are not more
  ;; than 1000 in abs value.
  (do ((c a (cdr c))
       (d b (cdr d))
       (ans 0 (+ ans (the fixnum (* (the mod-nn (car c))
				    (the (integer -1000 1000) (car d)))))))
      ((null c) ans)
    (declare (fixnum ans))))

(defun winnow-orbit (orb)
  ;; On input, orb is of the form ((cpt1 . sign1) (cpt2 . sign2) ...).
  ;; On output, ans is of the same form, but winnowed.  The output
  ;; itself is either ans, or nil if some point cpt_i occurs twice with
  ;; opposite signs.
  (do ((orbit orb)
       (temp '())
       (ans '())
       (run nil))
      (nil) ; ends with one of two explicit returns
    (cond ((null orbit)
	   (cond ((null temp)
		  (return ans)) ; done
		 (t ; done with one cycle
		  (psetq orbit temp
			 temp orbit
			 run nil))))
	  ((not run)
	   ;; time to put a new (pt . sgn) on the front of the ans.
	   ;; We'll then test all other elements (they'll all be in
	   ;; orbit at this point) against this one, putting those
	   ;; whose car's don't match into temp.
	   (push (pop orbit) ans)
	   (setq run t))
	  ;; If you're here, keep comparing (car orbit) to (car ans)
	  ((= (the cpt (caar orbit))
	      (the cpt (caar ans)))	; a pt is occurring twice
	   (cond ((= (the fixnum (cdar orbit)) 
		     (the fixnum (cdar ans)))
		  ;; No conflict; simply throw this (car orbit) away.
		  (pop orbit))
		 (t
		  ;; Conflict!
		  (return nil)))) ; from the do, i.e. the whole function
	  (t ; a pt irrelevant on this pass; put it onto temp
	   (push (pop orbit) temp)))))

;;; Here is a function, equivalent to (winnow-orbit (make-orbit gp x))
;;; [i.e. output is the same as a set], but potentially more
;;; efficient.  It can't be used in PARSE because we need both y and z
;;; there.

(defun make-winnowed-orbit (gp x)
  ;; gp  is as in parse.  x is a CPT in P^3.  Output is the list of pairs
  ;; (cpt . s) for all g in  gp , where cpt = x*g and  s  is the sign of
  ;; g.  There are no duplicates in the answer.  If for any CPT y,
  ;; both (y . 1) and (y . -1) would be on the list, then the whole
  ;; answer is nil.
  (declare (type cpt x))
  (let ((x-ppt (cpt-to-ppt x))
	(plus-list '())
	(minus-list '())
	(y 0)) ; dummy value
    (declare (type cpt y))
    (dolist (g gp
	       ;; Final result:
	       (nconc (mapcar #'(lambda (a)
				  (declare (type cpt a))
				  (cons a 1))
			      plus-list)
		      (mapcar #'(lambda (a)
				  (declare (type cpt a))
				  (cons a -1))
			      minus-list)))
      (setq y (ppt-to-cpt
	       (proj-nice
		(mapcar #'(lambda (col)
			    (the fixnum (list-dot x-ppt col)))
			(car g)))))
      (cond ((= 1 (the fixnum (cdr g)))
	     (if (member y minus-list :test #'=)
		 (return nil) ; stop immediately
	       (pushnew y plus-list)))
	    (t ; (= -1 (cdr g))
	     (if (member y plus-list :test #'=)
		 (return nil)
	       (pushnew y minus-list)))))))

(defun our-set-difference (a b)
  "Set difference 'a minus b' of lists of distinct fixnums where a is
already sorted by less-than.  The method sorts b in place.  The result
may share top-level list structure with a."
  (declare (list a b))
  (setq b (sort b #'(lambda (m n) (< (the fixnum m) (the fixnum n)))))
  (let ((a-tail a) (b-tail b) (ans '()))
    (declare (list a-tail b-tail ans))
    (till (or (endp a-tail) (endp b-tail))
      (let ((a0 (car a-tail))
	    (b0 (car b-tail)))
	(declare (fixnum a0 b0))
	(when (< a0 b0)
	  (push a0 ans))
	(when (<= a0 b0)
	  (pop a-tail))
	(when (>= a0 b0)
	  (pop b-tail))))
    (nreconc ans a-tail)))

(defun our-set-difference-equal (a b)
  ;; The system's makes the value stack overflow.  Is it recursive
  ;; where it should be iterative?
  ;;    The test is #'EQUAL.
  (let ((ans '()))
    (dolist (x a)
      (when (not (member x b :test #'equal))
	    (push x ans)))
    (nreverse ans)))

(defun code-and-sign-collapse (lyst ar n)
  ;; Input is a list of elts (codenum . val) .  Output is the same,
  ;; but all pairs with the same codenum will be collapsed into one,
  ;; and the values will be summed.  The codenum's run through [0,n) .
  ;; ar is a dummy array of length >= n which will be used as an
  ;; accumulator.
  (declare (simple-vector ar)
	   (fixnum n))
  (fill ar 0 :start 0 :end n)
  (dolist (pair lyst)
    (incf (the fixnum (svref ar (the fixnum (car pair))))
	  (the fixnum (cdr pair))))
  (do ((i (1- n) (1- i))
       (ans '())
       (v 0))
      ((< i 0) ans)
    (declare (fixnum i v))
    (when (not (zerop (setq v (svref ar i))))
      (push (cons i v) ans))))    

(defun fac-d1 (orep6 oreps5 table5 pt-to-orep-5 gp6 gp5 gp65
		     &optional (magic +1))
  ;; orep6 is an orbit rep've for gp6.  orb6 is its orbit.  For each
  ;; suborb6--a sub-gp65 orbit within orb6--and for each elt orb5 in
  ;; the set of orbits rep'd by oreps5, check if orb5 has an elt (pt .
  ;; s) s.t. suborb6 has an element (pt . s') .  [It follows from the
  ;; def'n of gp65, as an intersection of the groups stab6 and stab5x
  ;; (which are consistent on the signs) that if (pt0 . s0) and (pt0 .
  ;; s0') are also present on the respective lists, then s/s' =
  ;; s0/s0'.]  [The pts here are all CPT's.]  Push onto  ans  the pair
  ;;               ([code number of pt] . tt) ,
  ;; where tt = s * s' * magic * transfer-map-index .  gp6 is the
  ;; stabilizer of the std cell of type type6, and gp5 similarly.
  ;; gp65 is their intersection.
  ;;    In the equivariant homology version, the transfer-map-index
  ;; was [(subgp of gp6 fixing pt) : (subgp of gp65 fixing pt)].  In
  ;; this equivariant cohomology version, we are guessing it's
  ;; [(subgp of gp5 fixing pt) : (subgp of gp65 fixing pt)].
  ;;    Even when all the standard cells are given +1 orientation, it
  ;; is impossible to orient them consistently so that all the
  ;; relative orientations (Brown's $\partial_{\sigma\tau}$) are
  ;; +1. The magic number is a correction factor.
  ;;   In everything here, 6 and 5 may be replaced by 5 and 4, resp.
  (declare (type cpt orep6)
	   (ignore oreps5)
	   (type (integer -1 1) magic)
	   (simple-vector table5 pt-to-orep-5))
  (let* ((orb6 (make-winnowed-orbit gp6 orep6))
	 (suborb6-lyst (parse-porting-signs gp65 orb6 '()))
	 (ans '())
	 orb5
	 pair6 pair5)
    (dolist (suborb6 suborb6-lyst)
      (block got-a-match
       (let ((possible-oreps5
	      ;; Originally, possible-oreps5 was just oreps5.  But,
	      ;; using the table pt-to-orep-5, we can identify the few
	      ;; elements orep5 of oreps5 which are capable of passing
	      ;; the test below.
	      (remove-duplicates
	       (mapcar #'(lambda (a)
			   (svref pt-to-orep-5 (the cpt (car a))))
		       suborb6)
	       :test #'=)))
	(dolist (orep5 possible-oreps5)
	  (declare (type cpt orep5))
	  (setq orb5 (make-winnowed-orbit gp5 orep5))
	  ;; suborb6 and orb5 are orbits, ((cpt . s) ...)
	  (setq pair6 nil
		pair5 nil)
	  (dolist (a suborb6)
	    (dolist (b orb5)
	      ;; a and b are pairs (cpt . s)
              (when (= (the cpt (car a)) (the cpt (car b)))
		(return-from got-a-match
		  (setq pair6 a
			pair5 b))))))))
      (when (not (null pair6))
	(push
	 (cons (the fixnum (svref table5 (the cpt (car pair5))))
	       (the fixnum
		    (* (the fixnum
			    (* (the fixnum (cdr pair6))
			       (the fixnum (cdr pair5))))
		       (the fixnum
			    (* magic
			       ;; The transfer map index.  It would be
			       ;; better if the lengths weren't
			       ;; recomputed every time.
			       ;; In the equivariant homology version,
			       ;; gp5 and orb5 below were gp6 and orb6.
			       (the fixnum
				    (/ (the fixnum
					    (* (the fixnum
						    (length gp5))
					       (the fixnum
						    (length suborb6))))
				       (the fixnum 
					    (* (the fixnum
						    (length gp65))
					       (the fixnum
						    (length orb5))))))
			       )))))
	 ans)))
    ans))

(defun parse-porting-signs (group orbit ans)
  ;; Here group is a list of (matrix . sign)
  ;; pairs.  orbit is a list of pairs (cpt . sign) [not a list of
  ;; pts].  The output is a list of suborbits mod the new group.  Each
  ;; suborbit is a list of pairs (pt . sign), where the sign is merely
  ;; copied--"goes along for the ride"--sort of....
  (cond ((null orbit)
	 ans)
	(t
	 (let* ((s (cdar orbit))
		(z (cpt-to-ppt (the cpt (caar orbit))))
		(x (remove-duplicates
		    (mapcar #'(lambda (g) (parse-aux g z)) group)
		    :test #'equal))
		;; x = ((cpt . s') ...) .  Must multiply all the s' by
		;; s to make them match the signs already in  orbit .
		(y (if (= s 1)
		       x
		     (mapcar #'(lambda (pair)
				 (cons (the cpt (car pair))
				       (the fixnum (- (the fixnum
							   (cdr pair))))))
			     x))))
	   (declare (fixnum s))
	   ;; Tail-recurse
	   (parse-porting-signs group
				(our-set-difference-equal orbit y)
				(cons y ans))))))
