(in-package shh2)

(declaim (optimize safety debug))

;;; Programs to study the topology of two-complexes.

;;; This is the March 15, 2005 version, unchanged, of two-complex.
;;; After the line for Sept. 2, there are additions so it can be used
;;; for testing homolalg.  For a more elaborate version of two-complex
;;; with geometry in R^3 and minimal surfaces, see shh2ILC05.

;;; A simplex is a list of distinct integers sorted by <.  An
;;; n-dimensional simplex (or n-simplex) has n+1 elements.  This
;;; package uses 0-simplices (vertices), 1-simplices (edges), and
;;; 2-simplices (triangles).

(defun sx-boundary (sx)
  "Lists all the (i-1) dimensional faces of the i-simplex sx.
The usual orientation convention for simplicial complexes
holds: the orientation of the j-th face in the list is (-1)^j."
  (mapcar #'(lambda (x) (remove x sx)) sx))

;;; A polygon is a list of three or more distinct integers.
;;; For instance, (0 1 2 3) is this square:
;;; 0 - 1
;;; |   |
;;; 3 - 2
;;; The code automatically splits the square into two 2-simplices:
;;; 0 - 1
;;; | \ |
;;; 3 - 2

(defun triangulate-polygon (polygon &optional (ans '()))
  (if (endp (cddr polygon))
      (nreverse ans)
    (destructuring-bind (a b c &rest rest) polygon
      (declare (ignore rest))
      (triangulate-polygon
       (cons a (cddr polygon)) ;; remove b
       (cons (list a b c) ans)))))
   
;;; Main definition.

(defclass two-complex ()
  ((sx-tables :documentation
              "The keys of (svref sx-tables i) are the
i-simplices.  Values are indices 0, 1, 2, ... into the
rows and columns of the boundary matrices.")
   (d1 :initform nil
       ;; accessor (d1 ...) defined below
       :documentation
       "Map from simplicial 1-chains to 0-chains, as an snf.
Evaluated lazily, so always use the accessor to read it.")
   (d2 :initform nil
       ;; accessor (d2 ...) defined below
       :documentation
       "Map from simplicial 2-chains to 1-chains, as an snf.
Evaluated lazily, so always use the accessor to read it."))
  (:documentation
   "A two-complex is built by gluing vertices, edges and
polygons together along their faces.  Examples include
the surfaces of the sphere, torus, and Klein bottle.  Use
make-two-complex to construct a two-complex.  The complex
computing the homology is
C_0 <-- d1 -- C_1 <-- d2 -- C_2."))

(defparameter *torus-cells*
    ;; Take the nine 1-by-1 squares with these vertices.  Notice how
    ;; the top and bottom edges are glued together and the left and
    ;; right edges are glued together.
    ;; 0 1 2 0
    ;; 6 7 8 6
    ;; 3 4 5 3
    ;; 0 1 2 0
    (list '(6 7 1 0) '(7 8 2 1) '(8 6 0 2)
          '(3 4 7 6) '(4 5 8 7) '(5 3 6 8)
          '(0 1 4 3) '(1 2 5 4) '(2 0 3 5))
  "Sample data: (make-two-complex *torus-cells*) gives
a torus.")

(defparameter *klein-bottle-cells*
    ;; Same as in *torus-cells*, but invert the top row so
    ;; that the bottom edge is glued to it backwards.
    ;; 0 2 1 0
    ;; 6 7 8 6
    ;; 3 4 5 3
    ;; 0 1 2 0
    (list '(6 7 2 0) '(7 8 1 2) '(8 6 0 1)
          '(3 4 7 6) '(4 5 8 7) '(5 3 6 8)
          '(0 1 4 3) '(1 2 5 4) '(2 0 3 5))
  "Sample data: (make-two-complex *klein-bottle-cells*) gives
a Klein bottle.")

(defparameter *sphere-cells*
    (sx-boundary '(0 1 2 3)) ;; boundary of a 3-simplex
  "Sample data: (make-two-complex *sphere-cells*) gives
a sphere.")

(defun make-two-complex (cells)
  "Cells is a list of items to be glued together to make a
two-complex.  An length-1 list is a 0-simplex [vertex].  A length-2
list is a 1-simplex [edge].  A length-3 list is a 2-simplex
[triangle].  A length-n list is an n-sided polygon, which is
automatically divided into 2-simplices.  The return value is a
two-complex data structure."
  (let ((cx (make-instance 'two-complex))
	(cells0 (copy-list cells)))
    (with-slots (sx-tables) cx
      (setq sx-tables (make-array '(3)))
      (dotimes (i 3)
        (setf (svref sx-tables i) (make-hash-table :test #'equal)))
      (let ((vals (make-array '(3) :initial-element 0)))
        (labels ((add-if-new (sx i)
                   (let ((table (svref sx-tables i)))
                     (unless (nth-value 1 (gethash sx table))
                       (setf (gethash sx table) (svref vals i))
                       (incf (svref vals i))
                       (when (> i 0)
                         (mapcar #'(lambda (face) (add-if-new face (1- i)))
                                 (sx-boundary sx)))))))
          (with-splicer cells0
            (till (splicer-endp)
              (let ((cell (splicer-read)))
                (assert (and (listp cell) (every #'integerp cell)
                             (not (endp cell)))
                    (cell)
                  "Cell ~S should be a non-empty list of distinct integers."
                  cell)
                (unless (endp (cdddr cell))
                  ;; Replace polygon of >= 4 sides with triangulation.
                  (splicer-delete)
                  (dolist (triangle (triangulate-polygon cell))
                    (splicer-insert triangle))
                  (setq cell (splicer-read)))
                (let ((i (1- (length cell)))) ;; cell is an i-simplex
                  (unless (zerop i)
                    (setq cell (sort (copy-list cell) #'<))
                    (assert (every #'/= cell (rest cell)) (cell)
                      "Cell ~S should have no repeated elements." cell)
                    (splicer-modify cell))
                  (add-if-new cell i)
                  (splicer-fwd))))))))
    cx))

(defmethod d1 ((cx two-complex))
  "The map from simplicial 1-chains to 0-chains, as an snf."
  (with-slots (d1) cx
    (aif d1 it (setf d1 (make-d cx 1)))))
    
(defmethod d2 ((cx two-complex))
  "The map from simplicial 2-chains to 1-chains, as an snf."
  (with-slots (d2) cx
    (aif d2 it (setf d2 (make-d cx 2)))))
    
(defvar *two-complex-make-sp* #'make-sp-z)
    
(defmethod make-d ((cx two-complex) (i integer))
  "The user should call d1 and d2, not this method."
  (with-slots (sx-tables) cx
    (let ((ci (svref sx-tables i)) ;; i-chains
          (ci1 (svref sx-tables (1- i)))) ;; (i-1)-chains
      (let ((m (hash-table-count ci1))
            (n (hash-table-count ci)))
        (let ((a (make-csparse-zero m n)))
          ;; The mapping is (i-1)-chains <--a-- i-chains.
          (with-hash-table-iterator (next-sx ci)
            (loop
              (multiple-value-bind (present-p sx j) (next-sx)
                (if present-p
                    (do ((faces (sx-boundary sx) (rest faces))
                         (entry 1 (- entry))) ;; alternating sign
                        ((endp faces))
                      (let ((i (gethash (first faces) ci1)))
                        (assert (not (null i)) ()
                          "Missing face ~S" (first faces))
                        (csparse-set a (funcall *two-complex-make-sp* i entry)
				     j)))
                  (return (make-snf a)))))))))))

(defmethod print-homology ((cx two-complex) &optional (stream t))
  "Prints to stream the ranks and torsion coefficients of the
homology H_*(cx, Z) of the two-comples cx."
  (format stream "~&H_0 is free of rank ~D"
          (- (m-num-rows (d1 cx)) (rank (d1 cx))))
  (format stream "~&H_1 has free part of rank ~D and torsion coeffs ~S"
          (- (m-num-cols (d1 cx)) (rank (d1 cx)) (rank (d2 cx)))
          (mapcar #'sp-integer-value (mapcar #'sp-pretty-associate (torsion (d2 cx)))))
  (format stream "~&H_2 is free of rank ~D"
          (- (m-num-cols (d2 cx)) (rank (d2 cx)))))

;;; ------------------------- September 2, 2005 -------------------------

(defmethod make-cochain-cx-2 ((cx two-complex))
  (let ((c2 (make-instance 'free-z-module :rank (m-num-cols (d2 cx))))
	(c1 (make-instance 'free-z-module :rank (m-num-rows (d2 cx))))
	(c0 (make-instance 'free-z-module :rank (m-num-rows (d1 cx))))
	(diffs (make-hash-table :test #'eql :size 2)))
    (puthash -2 (make-csparsez-mfm c2 c1 (d2 cx)) diffs)
    (puthash -1 (make-csparsez-mfm c1 c0 (d1 cx)) diffs)
    (make-ccx nil diffs)))

(defun test-cochain-cx-2 (cells h0 h1 h2 tor1)
  "Finds the homology Betti numbers of the two-complex for 'cells',
asserting that they are h0, h1, h2 for H_0, H_1, H_2.  Also
asserts that the torsion coefficients in H_1 are as in tor1,
and that H_0 and H_2 have no torsion."
  (declare (list cells) (type (integer 0 *) h0 h1 h2) (list tor1))
  (let ((cochain-cx-2 (make-cochain-cx-2 (make-two-complex cells))))
    (declare (type ccx cochain-cx-2))
    (labels ((test-i (i h tor)
	       (declare (integer i) (type (integer 0 *) h) (list tor))
	       (multiple-value-bind (b btor) (betti-numbers cochain-cx-2 i)
		 (declare (type (integer 0 *) b) (list btor))
		 (assert (= b h) ()
		   "The ~:R Betti number is ~D, but we expected ~D."
		   (- i) b h)
		 (setq btor (mapcar #'abs btor))
		 (assert (equal tor btor) ()
		   "The torsion coeffs in deg ~D are ~S, but we expected ~S."
		   (- i) btor tor))))
      (test-i 0 h0 '())
      (test-i -1 h1 tor1)
      (test-i -2 h2 '()))))

;;; Unit tests.
(test-cochain-cx-2 *torus-cells* 1 2 1 '())
(test-cochain-cx-2 *klein-bottle-cells* 1 1 0 '(2))
(test-cochain-cx-2 *sphere-cells* 1 0 1 '())
