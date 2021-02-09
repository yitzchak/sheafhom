(in-package shh2)

;;; This file contains functions that use features outside the ANSI
;;; Common Lisp standard and must be written differently for different
;;; Common Lisp implementations.  show-line-graph runs a graphical
;;; utility to show a simple line graph.  Other functions offer a
;;; "csparse window" (csw); as a sparse matrix is reduced, the window
;;; displays the changing sparsity pattern.

;;; The implementations here are specific to Allegro CL 8.0.  They
;;; link to Java using Allegro's jlinker.

;;; HOW TO USE THIS FILE
;;; [.] If you don't have Allegro CL, jlinker or Java, or simply don't
;;;     need to use the GUI features, please COMMENT OUT everything
;;;     between the lines "ALLEGRO JLINKER GUI" and "NO GUI", and
;;;     uncomment everything below the line "NO GUI".
;;; [.] If you do have Allegro CL, jlinker and Java, please edit the
;;;     lines marked EDIT to match your installation.
;;; [.] In either case, also check the three variables
;;;     *multi-file-[...]* in multi-file.lisp.  It's recommended
;;;     to set them to functions that compress files using gzip, bzip2
;;;     or another utility.  See the sample code in multi-file.lisp.

;;; -------------------- ALLEGRO JLINKER GUI --------------------

#|
(setf (sys:getenv "CLASSPATH")
  (concatenate 'string
    (sys:getenv "CLASSPATH")
    ;; ***EDIT THE NEXT LINE TO MATCH YOUR INSTALLATION***
    ";C:\\Program Files\\acl80\\jlinker\\jlinker.jar;shh22.jar"))

(eval-when (:compile-toplevel)
  (require :jlinker)
  (use-package :javatools.jlinker))

;; ***EDIT THE NEXT LINE TO MATCH YOUR INSTALLATION***
(load "C:\\Program Files\\acl80\\jlinker\\jl-config")

;;; Note [August 6, 2007]: We tested the native version of jlinker on
;;; ACL 8.0.  The only changes were to delete the form above that sets
;;; CLASSPATH, and to replace the calls (jlinker-init) below with
;;; (jlinker-init :native :jar "C:\\Program Files\\acl80\\jlinker\\jlinker.jar" :classpath "C:\\mark\\math\\shh2\\shh22.jar")
;;; Surprisingly, the native version didn't run faster, perhaps even
;;; slower, and the painting was jagged.  Too many immediate repaints?

;;; ------------------------------------------------------------

(defun show-line-graph (v title &optional (max-points (length v)))
  "Display a line graph whose y-coordinates are the elements of the
sequence v.  These elements must be numbers.  The x-coordinates
are equally spaced.  The number of points in the graph is the lesser
of max-points and the length of v."
  (let* ((n (length v))
	 (v-dbl (make-array (list n) :element-type 'double-float)))
    (declare (type (array double-float *) v-dbl))
    (map-into v-dbl #'(lambda (x) (coerce x 'double-float)) v)
    (or (jlinker-query t) (jlinker-init)) ;; start the JVM, if necessary
    (jstatic "show" "shh2.javasrc.StatWin" v-dbl title max-points)))
  
;;; ------------------------------------------------------------

(defvar *csw* nil
  "A 'csparse window' showing the changing sparsity pattern of
a csparse as it is reduced.")

(defun csw-init (title m n)
  "Create a new csw and show it."
  (declare (string title) (fixnum m n))
  (let ((max-width 900)
	(max-height 600)) ;; change to fit your screen
    (let ((delta (max (ceiling n max-width)
                      (ceiling m max-height)
                      1)))
      (declare (fixnum delta))
      (let ((w (ceiling n delta))
            (h (ceiling m delta)))
        (declare (fixnum w h))
	(or (jlinker-query t) (jlinker-init)) ;; start the JVM, if necessary
        ;; Killing a CSparseWin0 kills the JVM.  That's convenient for
        ;; the user, but it means we can't kill the old csw here.
        (setq *csw* (jnew "shh2.javasrc.CSparseWin0" title m n w h delta))
        (jcall "show" *csw*)
        (values delta w h)))))

(defun csw-set-corner (corner)
  "Sets the boundary of the active region in the csw, if a csw exists."
  (declare (fixnum corner))
  (when *csw*
    (jcall "setCorner" *csw* corner)))

(defun csw-set-note (note)
  "Sets a text note in the csw, if a csw exists."
  (declare (string note))
  (when *csw*
    (jcall "setNote" *csw* note)))

(defun csw-set-yellow (a b)
  "Paints the csw yellow in columns a to b, if a csw exists."
  (declare (fixnum a b))
  (when *csw*
    (jcall "setYellow" *csw* a b)))

(defun csw-set-counter (counter)
  "Resets the painted portion of the csw, if a csw exists."
  (declare (type (array (signed-byte 32) *) counter))
  (when *csw*
    (jcall "setCounter" *csw* counter)))

(defun csw-is-active ()
  "Whether the csw exists and is the active window."
  (and *csw* (jcall "isActive" *csw*)))
|#

;;; --- NO GUI --- NO GUI --- NO GUI --- NO GUI --- NO GUI ---

;;; If you don't have Allegro CL and jlinker, or simply don't need to
;;; use the GUI features, please comment out everything above this
;;; point, and uncomment everything below.

(defun show-line-graph (v title &optional max-points)
  (declare (ignore v title max-points)))

(defun csw-init (title m n)
  (declare (ignore title m n))
  (values 1 0 0))

(defun csw-set-corner (corner)
  (declare (ignore corner)))

(defun csw-set-note (note)
  (declare (ignore note)))

(defun csw-set-yellow (a b)
  (declare (ignore a b)))

(defun csw-set-counter (counter)
  (declare (ignore counter)))

(defun csw-is-active ()
  nil)
