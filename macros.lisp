(in-package shh2)

(defmacro aand (&rest args)
  "Anaphoric and, from Graham's _On Lisp_.  As each form is
evaluated, the symbol 'it' is bound to the form's value while
evaluating the later forms."
  (cond ((null args) t)
        ((null (cdr args)) (car args))
        (t `(aif ,(car args) (aand ,@(cdr args))))))

(defmacro aif (test-form then-form &optional else-form)
  "Anaphoric if, from Graham's _On Lisp_.  As the body is
evaluated, the symbol 'it' is bound to the value of the test."
  `(let ((it ,test-form))
     (if it ,then-form ,else-form)))

(defmacro awhen (test-form &body body)
  "Anaphoric when, from Graham's _On Lisp_.  As the body is
evaluated, the symbol 'it' is bound to the value of the test."
  `(aif ,test-form
     (progn ,@body)))

(defmacro awhile (expr &body body)
  "Anaphoric while, from Graham's _On Lisp_.  The body is executed
repeatedly with the symbol 'it' bound to the value of expr, until
expr becomes nil."
  `(do ((it ,expr ,expr))
       ((not it))
     ,@body))

(deftype nnfixnum ()
  "The type of a non-negative fixnum."
  `(integer 0 ,most-positive-fixnum))

(defmacro dotimes-f ((i n &optional ans) &body body)
  "Dotimes for fixnums: declares i and n fixnum, i >= 0."
  `(dotimes ,(if ans `(,i (the fixnum ,n) ,ans) `(,i (the fixnum ,n)))
     (declare (type nnfixnum ,i))
     ,@body))

(defmacro format-flat (&rest args)
  "Same as (format [args]) with the pretty-printer turned off."
  `(let ((*print-pretty* nil))
     (format ,@args)))

(define-modify-macro maxf (&rest args)
  max
  "Set the first arg to the max of all the args.")

(define-modify-macro minf (&rest args)
  min
  "Set the first arg to the min of all the args.")

(defmacro puthash (key val table)
  "The set method for a hash-table."
  `(setf (gethash ,key ,table) ,val))

(define-modify-macro sortf (&rest args)
  sort
  "The form (sortf seq pred) is equivalent to (setf seq (sort seq pred)).")

(defmacro till (test &body body)
  `(do ()
       (,test)
     ,@body))

(defmacro with-gensyms (syms &body body)
  `(let ,(mapcar #'(lambda (s) `(,s (gensym))) syms)
     ,@body))

(defmacro with-splicer (place &body body)
  "A mini-language for surgery on lists.  'place' should evaluate to a
proper list (a ... b y ...).  The splicer has a head that starts from
the first element of the list and runs forward.  (In the examples
below, the head is at y.)  The macro sets up the following forms, of
which the last five destructively modify the underlying list.
Throughout, 'place' always evaluates to the modified list.  Calls to
with-splicer can be nested.
[.] (splicer-read) => return the element y currently under the head
[.] (splicer-tail) => return the sublist (y ...)
[.] (splicer-fwd) => move the head forward
[.] (splicer-endp) => true iff there are no more elements
[.] (splicer-insert x) => insert x before y; reposition the head at x
[.] (splicer-modify x) => replace y with x; leave the head there
[.] (splicer-delete) => delete y, putting the head at the next position
[.] (splicer-nconc l) => discard (y ...); nconc l onto the end
                         of (... b); put head at start of l
[.] (splicer-split) => reset place to the front sublist (a ... b), and
                       return three values:
                         the front sublist
                         last cons (b) of front [nil if front is empty]
                         the tail (y ...)"
  (with-gensyms (prev ptr)
    (macrolet ((check (num-args)
                 `(assert (= (length (rest code)) ,num-args) (code)
                    "Should have ~D arg~:P in ~S" ,num-args code)))
      (labels ((subs (code)
                 (if (atom code)
                     code
                   (case (first code)
                     (splicer-tail
                      (check 0)
                      ptr)
                     (splicer-read
                      (check 0)
                      `(first ,ptr))
                     (splicer-endp
                      (check 0)
                      `(endp ,ptr))
                     (splicer-fwd
                      (check 0)
                      `(setq ,prev ,ptr
                             ,ptr (rest ,ptr)))
                     (splicer-delete
                      (check 0)
                      `(progn
                         (pop ,ptr)
                         (if (endp ,prev)
                             (setf ,place ,ptr)
                           (rplacd ,prev ,ptr))))
                     (splicer-insert
                      (check 1)
                      `(progn
                         (push ,(second code) ,ptr)
                         (if (endp ,prev)
                             (setf ,place ,ptr)
                           (rplacd ,prev ,ptr))))
                     (splicer-modify
                      (check 1)
                      `(rplaca ,ptr ,(second code)))
                     (splicer-nconc
                      (check 1)
                      `(progn
                         (setq ,ptr ,(second code))
                         (if (endp ,prev)
                             (setf ,place ,ptr)
                           (rplacd ,prev ,ptr))))
                     (splicer-split
                      (check 0)
                      `(progn
                         (if (endp ,prev)
                             (setf ,place '())
                           (rplacd ,prev nil))
                         (values ,place ,prev ,ptr)))
                     (with-splicer
                         ;; Wait till next pass of macroexpansion.
                         code)
                     (t 
                      (cons (subs (car code)) (subs (cdr code))))))))
        `(let ((,prev nil)
               (,ptr ,place))
           (declare (list ,prev ,ptr))
           ,@(subs body))))))
