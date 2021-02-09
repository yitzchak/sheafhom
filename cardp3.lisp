(in-package cl-user)

(defconstant +cardP3+
  (let ((ans 1))
    (dolist (pair (factor +nn+) ans)
      (let ((p (car pair))
	    (e (cdr pair)))
	(setq ans (* ans
		     (expt p (* 3 (1- e)))
		     (+ 1 p (* p p) (* p p p)))))))
  "The number of points in P^3(Z/(+nn+)Z).")
