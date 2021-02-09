(in-package shh2)

(declaim (optimize speed))

(deftype dense-matrix-z ()
  "The type of m-by-n arrays with values in the ring of integers Z."
  '(simple-array integer (* *)))

(defun make-dense-matrix-z (m n)
  "Makes a dense-matrix-z of size m by n with all entries 0."
  (make-array (list m n) :element-type 'integer :initial-element 0))

(defun do-lll (A)
  "Does LLL reduction on the columns of the dense-matrix-z A,
destructively, using Algorithm 2.7.2 in Henri Cohen's book.  Returns
kerdim, the rank of the kernel as a free Z-module.  On output, the
columns j for kerdim <= j < n are a Z-basis of the lattice generated
by the columns of the input."
  (declare (type dense-matrix-z A))
  (macrolet ((get-lam (k l)
               `(the integer
                  (svref (the simple-vector (svref lam (the nnfixnum ,k)))
                         (the nnfixnum ,l))))
             (set-lam (i j value)
               `(progn
                  (unless (svref lam ,i)
                    (setf (svref lam ,i)
                      (make-array ,i)))
                  (setf (svref (the simple-vector
                                 (svref lam (the nnfixnum ,i)))
                               (the nnfixnum ,j))
                    (the integer ,value))))
             (get-d (l)
               `(the integer (svref d (the nnfixnum ,l))))
             (get-f (l)
               `(= (the bit (sbit f (the nnfixnum ,l))) 1))
	     (div-exact (a b)
	       ;; (/ a b) when we know remainder is 0.  Tests show it's
	       ;; faster than (/ a b).
	       `(the integer
		  (truncate (the integer ,a) (the integer ,b)))))
    (let ((m (array-dimension A 0))
          (n (array-dimension A 1)))
      (declare (type nnfixnum m n))
      (when (zerop n)
        (return-from do-lll 0))
      ;; Step 1
      (let ((k 1)
            (k-max 0)
            (d (make-array n :initial-element 0))
            (f (make-array n :element-type 'bit :initial-element 1))
            ;; The initial 1 in f is by Mark 12/5/03, for left0 below.
            (lam (make-array n)))
        (declare (type nnfixnum k k-max)
                 (type simple-vector d lam)
                 (type simple-bit-vector f))
        (let ((tt (dense-col-dot A 0 0 m)))
          (declare (integer tt))
          (if (zerop tt)
              (setf (svref d 0) 1 (aref f 0) 0)
            (setf (svref d 0) tt (aref f 0) 1)))
        ;; (If you want a progress monitor, initialize it here.)
        (till (>= k n)
          ;; Step 2
          ;; (If you have a progress monitor, tell it you're at k.)
          (dotimes-f (left0 n) ;; Mark's use of left0, 12/5/03
            (if (get-f left0)
                (return)
              (setf (svref lam left0) nil)))
          ;; If k <= k-max, go to step 3.
          (unless (<= k k-max)
            (setq k-max k)
            (do ((j 0 (1+ j)))
                ((> j k))
              (declare (type nnfixnum j))
              (if (and (< j k) (not (get-f j)))
                  (set-lam k j 0)
                (let ((u (dense-col-dot A k j m)))
                  (declare (integer u))
                  (dotimes-f (i j)
                    (when (get-f i)
                      (setq u (the integer
                                (- (the integer (* (get-d i) u))
                                   (the integer (* (get-lam k i)
                                                   (get-lam j i))))))
                      (when (>= i 1)
                        ;; At i = 0, divide by d[-1] := 1.
                        (setq u (div-exact u (get-d (1- i)))))))
                  (if (< j k)
                      (set-lam k j u)
                    (when (= j k)
                      (if (zerop u)
                          (setf (svref d k) (get-d (1- k))
                                (aref f k) 0)
                        (setf (svref d k) u
                              (aref f k) 1))))))))
          ;; Step 3
          (loop
            (when (get-f (1- k))
              (dense-redi A k (1- k) m d lam))
            (cond ((and (get-f (1- k)) (not (get-f k)))
                   ;; subroutine swapk(k)
                   (dense-col-swap A k (1- k) m)
                   (when (> k 1)
                     (do ((j 0 (1+ j)))
                         ((> j (- k 2)))
                       (declare (type nnfixnum j))
                       (let ((tmp (get-lam k j)))
                         (declare (integer tmp))
                         (set-lam k j (get-lam (1- k) j))
                         (set-lam (1- k) j tmp))))
                   (let ((lamb (get-lam k (1- k))))
                     (declare (integer lamb))
                     (cond ((zerop lamb)
                            (setf (svref d (1- k)) (if (>= k 2)
                                                       (get-d (- k 2))
                                                     1)
                              (aref f (1- k)) 0
                              (aref f k) 1)
                            (set-lam k (1- k) 0)
                            (do ((i (1+ k) (1+ i)))
                                ((> i k-max))
                              (declare (type nnfixnum i))
                              (set-lam i k (get-lam i (1- k)))
                              (set-lam i (1- k) 0)))
                           (t
                            (do ((i (1+ k) (1+ i)))
                                ((> i k-max))
                              (declare (type nnfixnum i))
                              (set-lam i (1- k)
				       (div-exact
					(* lamb (get-lam i (1- k)))
					(get-d (1- k)))))
                            (let ((tt (get-d k)))
                              (declare (integer tt))
                              (setf (svref d (1- k))
				(div-exact (* lamb lamb) (get-d (1- k))))
                              (setf (svref d k) (get-d (1- k)))
                              (do ((j (1+ k) (1+ j)))
                                  ((>= j k-max))
                                (declare (type nnfixnum j))
                                (do ((i (1+ j) (1+ i)))
                                    ((> i k-max))
                                  (declare (type nnfixnum i))
                                  (set-lam i j
					   (div-exact
					    (* (get-lam i j) (get-d (1- k)))
					    tt))))
                              (do ((j (1+ k) (1+ j)))
                                  ((> j k-max))
                                (declare (type nnfixnum j))
                                (setf (svref d j)
				  (div-exact
				   (* (get-d j) (get-d (1- k)))
				   tt)))))))
                   ;; end of subroutine swapk(k)
                   (setq k (max 1 (1- k))))
                  (t
                   (do ((l (- k 2) (1- l)))
                       ((< l 0))
                     (declare (fixnum l))
                     (when (get-f l)
                       (dense-redi A k l m d lam)))
                   (incf k)
                   (return))))) ;; go to step 4
        ;; Step 4 = go to step 2 while k < n.  Otherwise, ...
        ;; (If you have a progress monitor, tell it you're done.)
        (let ((kerdim 0))
          (declare (type nnfixnum kerdim))
          (till (or (>= kerdim n) (get-f kerdim))
            (incf kerdim))
          kerdim)))))

(defun dense-col-dot (A j0 j1 m)
  "Returns the dot product of columns in the dense-matrix-z A."
  (declare (type dense-matrix-z A) (type nnfixnum j0 j1 m))
  (let ((ans 0))
    (declare (integer ans))
    (dotimes-f (i m ans)
      (incf ans (the integer (* (the integer (aref A i j0))
                                (the integer (aref A i j1))))))))

(defun dense-col-swap (A j0 j1 m)
  "Interchanges columns in the dense-matrix-z A.  Returns the altered A."
  (declare (type dense-matrix-z A) (type nnfixnum j0 j1 m))
  (dotimes-f (i m A)
    (psetf (aref A i j0) (aref A i j1)
           (aref A i j1) (aref A i j0))))

(defun dense-redi (A k l m d lam)
  "Helper for do-lll."
  (declare (type dense-matrix-z A) (type nnfixnum k l m) (simple-vector d lam))
  (macrolet ((get-lam (k l)
               `(the integer
                  (svref (the simple-vector (svref lam (the nnfixnum ,k)))
                         (the nnfixnum ,l))))
             (set-lam (i j value)
               `(progn
                  (unless (svref lam ,i)
                    (setf (svref lam ,i)
                      (make-array ,i)))
                  (setf (svref (the simple-vector
                                 (svref lam (the nnfixnum ,i)))
                               (the nnfixnum ,j))
                    (the integer ,value))))
             (get-d (l)
               `(the integer (svref d (the nnfixnum ,l)))))
    (unless (<= (the integer (abs (the integer (* 2 (get-lam k l)))))
                (get-d l))
      (let ((q (round (get-lam k l) (get-d l))))
        (declare (integer q))
        (dotimes-f (i m)
          (decf (aref A i k)
                (the integer (* q (the integer (aref A i l))))))
        (set-lam k l
          (the integer (- (get-lam k l) (the integer (* q (get-d l))))))
        (dotimes-f (i l)
          (set-lam k i
            (the integer (- (get-lam k i)
                            (the integer (* q (get-lam l i)))))))))))

