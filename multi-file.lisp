(in-package shh2)

(defstruct multi-file
  "When the user has a large number of Lisp objects x to store and
reread from disk, a multi-file object mf will store them in one or
more compressed files, allowing the user to pretend the whole thing
is a single uncompressed file.
  Create mf with, e.g., (make-multi-file :stem cow :ext txt).  (Put
cow and txt in double-quotes when typing at a Lisp prompt.)  The x's
are stored in one or more files, with up to +multi-file-max-objs+
objects in each file.  In our example, the files will be named
cow.0.txt, cow.1.txt, etc.  Old files of the same name in the same
directory will be silently overwritten.
  To set up the compression, see *multi-file-compressor*,
*multi-file-compressed-namer*, and *multi-file-decompressor*.  If you
set these variables before loading this file, a unit test will run to
check them.
  For each x, call (multi-file-print x mf) to write x to the multi-file.
When the writing is done, call (multi-file-lock mf).  After locking,
do reading but no more writing.  Reading is documented at
multi-file-init-read, multi-file-read, and multi-file-peek."
  (stem "cow")
  (ext "txt")
  (count 0) ;; Number of objects overall.
  (fn -1) ;; Files are cow.i.txt for 0 <= i <= fn.
  (fni -1) ;; Runs 0 <= fni <= fn during reads.
  (locked nil)
  (stream nil))

(defconstant +multi-file-max-objs+ 20000)

(defvar *multi-file-compressor* nil
  "When non-nil [recommended], is a function that takes a filename and
compresses the file with a utility like gzip or bzip2.  Here is
an example for Allegro CL and bzip2 on Windows (take out the backslash
before the double-quotes).
  (setq *multi-file-compressor*
    (lambda (filename)
      (excl:run-shell-command
       (format nil \"\\bzip2\\bin\\bzip2 ~A\" filename)
       :wait t :show-window :hide)))")

(defvar *multi-file-compressed-namer* nil
  "When non-nil [recommended], is a function that converts a string like
cow.17.txt to the string cow.17.txt.gz, or cow.17.txt.bz2, or whatever
*multi-file-compressor* is going to yield.  Here is an example for
bzip2 (take out the backslash before the double-quotes).
  (setf *multi-file-compressed-namer*
    (lambda (filename)
      (format nil \"~A.bz2\" filename)))")

(defvar *multi-file-decompressor* nil
  "When non-nil [recommended], is a function that inverts
*multi-file-compressor*.  The input is the name of the compressed file.
E.g., calling the function on the string cow.17.txt.gz,
cow.17.txt.bz2, or whatever should decompress it to the file named
cow.17.txt.  Here is an example for Allegro CL and bzip2 on
Windows (take out the backslash before the double-quotes).
  (setq *multi-file-decompressor*
    (lambda (filename-bz2)
      (excl:run-shell-command
       (format nil \"\\bzip2\\bin\\bunzip2 ~A\" filename-bz2)
       :wait t :show-window :hide)))")

(defun multi-file-print (x mf)
  "Documented at multi-file.  Returns x."
  (assert (not (multi-file-locked mf)) ()
    "Can't print to a multi-file after it is locked.")
  (when (zerop (mod (multi-file-count mf) +multi-file-max-objs+))
    (multi-file-close mf)
    (incf (multi-file-fn mf))
    (setf (multi-file-stream mf)
      (open (multi-file-name mf)
	    :direction :output
	    :if-exists :supersede
	    :if-does-not-exist :create)))
  (format-flat (multi-file-stream mf) "~S " x)
  (incf (multi-file-count mf))
  x)

(defun multi-file-lock (mf)
  "Call this when you've finished writing to mf and are ready to read."
  (multi-file-close mf)
  (setf (multi-file-locked mf) t))

(defun multi-file-close (mf &optional (compress t))
  "Not to be called by the user.  The streams and files underlying mf
are closed automatically."
  (awhen (multi-file-stream mf)
    (close it)
    (setf (multi-file-stream mf) nil)
    (when compress
      (awhen *multi-file-compressor*
	(funcall it (multi-file-name mf))))))

(defun multi-file-name (mf &optional i)
  "Returns the string cow.i.txt in our example."
  (unless i
    (setq i (if (multi-file-locked mf)
		(multi-file-fni mf)
	      (multi-file-fn mf))))
  (format nil "~A.~D.~A" (multi-file-stem mf) i (multi-file-ext mf)))

(defun multi-file-init-read (mf)
  "Call to get mf ready for reading.  The internal pointers are
repositioned to the beginning of the multi-file."
  (assert (multi-file-locked mf) ()
    "Can't read from a multi-file until it is locked.")
  (multi-file-close mf)
  (setf (multi-file-fni mf) -1))  

(defun multi-file-read (mf)
  "Returns the next object in sequence from mf, or nil at end-of-file."
  (assert (multi-file-locked mf) ()
    "Can't read from a multi-file until it is locked.")
  (unless (aand (multi-file-stream mf) (peek-char t it nil))
    (multi-file-close mf)
    (cond ((< (multi-file-fni mf) (multi-file-fn mf))
	   (incf (multi-file-fni mf))
	   (let ((name (multi-file-name mf)))
	     (awhen *multi-file-decompressor*
		(funcall it (funcall *multi-file-compressed-namer* name)))
	     (setf (multi-file-stream mf) (open name :direction :input))))
	  (t
	   (return-from multi-file-read nil))))
  (read (multi-file-stream mf)))

(defun multi-file-peek (mf)
  "Returns the next character in mf [not the next Lisp object],
or nil if mf is at end of file.  The character is not popped off
the stream."
  (or (< (multi-file-fni mf) (multi-file-fn mf))
      (aand (multi-file-stream mf) (peek-char t it nil))))

(defun multi-file-delete (mf)
  "Deletes all of mf's underlying files from the disk.  If compression
is by bzip2, e.g., deletes cow.i.txt and cow.i.txt.bz2 for all i."
  (multi-file-close mf nil)
  (dotimes (i (1+ (multi-file-fn mf)))
    (let ((name (multi-file-name mf i)))
      (when (probe-file name)
	(delete-file name))
      (awhen *multi-file-compressed-namer*
	(let ((name-z (funcall it name)))
	  (when (probe-file name-z)
	    (delete-file name-z)))))))

;;; -------------------- Unit tests --------------------

(in-package "CL-USER")

;; Write 0,...,ct-1 to a multi-file, then read it back twice.  Use a
;; range of ct's.
(when (and *multi-file-compressor* *multi-file-compressed-namer*
	   *multi-file-decompressor*)
  (dolist (ct (list 67
		    shh2::+multi-file-max-objs+
		    (+ shh2::+multi-file-max-objs+ 67)
		    (* 2 shh2::+multi-file-max-objs+)
		    (1+ (* 2 shh2::+multi-file-max-objs+))))
    (let ((mf (make-multi-file :stem "mftest")))
      (dotimes (i ct)
	(multi-file-print i mf))
      (multi-file-lock mf)
      (dotimes (times-to-read 2)
	(multi-file-init-read mf)
	(do ((j 0 (1+ j))
	     (x (multi-file-read mf) (multi-file-read mf)))
	    ((= j ct)
	     (assert (null x)))
	  (assert (and x (eql j x)))
	  (unless (= j (1- ct))
	    (assert (multi-file-peek mf)))))
      (multi-file-delete mf))))
