(in-package shh2)

(declaim (optimize speed))

(defgeneric strongly-conn-vertices (g)
  (:documentation
"Returns an mset of all the vertices of the directed graph g.  See
strongly-conn-scc for more information."))

(defgeneric strongly-conn-num-vertices (g)
  (:documentation
"Returns the number of vertices of the directed graph g.  See
strongly-conn-scc for more information."))

(defgeneric strongly-conn-edges-from (g v)
  (:documentation
"Returns an mset of all the edges of the directed graph g that start
at the vertex v.  See strongly-conn-scc for more information."))

(defgeneric strongly-conn-ending-vertex (g e)
  (:documentation
"Returns the ending vertex of the edge e.  See strongly-conn-scc for
more information."))

(defun strongly-conn-scc (g &optional start-v)
  "Any object g that implements the four 'strongly-conn' generic
functions is a directed graph defined by the local conditions
expressed by those four functions.  The vertices and directed edges of
g can be any non-null objects, as long as equalp is a valid test for
equality among them.
  This function strongly-conn-scc finds the strongly-connected
components in g.  We use an algorithm of Tarjan as presented in Shimon
Even, _Graph Algorithms_, Computer Science Press, 1979, p. 65.
  The optional argument start-v is the vertex at which to start.
  The function returns a list of lists of vertices.  Each inner
list is a strongly-connected component.  The inner lists appear
in the order from sinks to sources.  Note that this is a partial
ordering, possibly with incomparable components."
  (macrolet ((make-table () '(make-hash-table :test #'equalp :size n))
	     (get-int (key table) `(the integer (gethash ,key ,table)))
	     (is-used (e) `(has-key ,e used-edges))
	     (mark-used (e) `(puthash ,e t used-edges)))
    ;; step1
    (let ((n (strongly-conn-num-vertices g)))
      (prog ((used-edges (make-table)) ;; INIT SIZE SHOULD BE #E, NOT #V
	     (k (make-table)) ;; v -> count 1,2,... in order of discovery
	     (f (make-table)) ;; v -> v's parent
	     (l (make-table)) ;; v -> v's integer lowpoint
	     (s '()) ;; stack of v's in order of discovery
	     (s-set (make-table)) ;; s as set
	     (i 0)
	     (v start-v) ;; the vertex we're working on
	     (e nil) ;; the edge we're working on
	     (u nil) ;; e is from v to u
	     (ans '()))
	(declare (hash-table used-edges k f l s-set) (list s ans) (integer i))
	(do-mset (v0 (strongly-conn-vertices g))
	  (unless v
	    (setq v v0))
	  (puthash v0 0 k))
	(unless v
	  (return '())) ;; empty graph
       step2
	(incf i)
	(puthash v i k)
	(puthash v i l)
	(push v s)
	(puthash v t s-set)
       step3
	(setq e nil)
	(do-mset (ee (strongly-conn-edges-from g v))
	  (unless (is-used ee)
	    (setq e ee)
	    (go step4)))
	(unless e
	  (go step7)) ;; all edges starting from v are used
       step4
	(setq u (strongly-conn-ending-vertex g e))
	(mark-used e)
	(when (zerop (get-int u k))
	  (puthash u v f)
	  (setq v u)
	  (go step2))
	;; step5
	(if (> (get-int u k) (get-int v k))
	    (go step3) ;; e is a forward edge
	  (unless (has-key u s-set)
	    (go step3))) ;; u and v don't belong to the same component
	;; step6 ;; k(u) < k(v) and u, v are in the same component
	(let ((ku (get-int u k)))
	  (declare (integer ku))
	  (when (< ku (get-int v l))
	    (puthash v ku l))
	  (go step3))
       step7
	(when (= (get-int v l) (get-int v k))
	  (let ((scc '()))
	    (declare (list scc))
	    (loop
	      (let ((v0 (pop s)))
		(remhash v0 s-set)
		(push v0 scc)
		(when (equalp v0 v)
		  (return))))
	    (push scc ans)))
	;; step8
	(multiple-value-bind (fv fv-defined-p) (gethash v f)
	  (when fv-defined-p
	    (let ((lv (get-int v l)))
	      (declare (integer lv))
	      (when (< lv (get-int fv l))
		(puthash fv lv l))
	      (setq v fv)
	      (go step3))))
	;; step9 ;; f(v) is undefined.  Get a fresh starting v, if any.
	(with-hash-table-iterator (k-iter k)
	  (loop
	    (multiple-value-bind (has-v0 v0 val) (k-iter)
	      (if has-v0
		  (when (zerop (the integer val))
		    (setq v v0)
		    (go step2))
		(return)))))
	;; step10
	(return (nreverse ans))))))

;;; ------------------------------------------------------------

(defclass strongly-conn-graph ()
  ((v-set :initarg :v-set
	   :documentation
	  "Mset of vertices v.  v's are non-null.  Equality is equalp.")
   (e-set :initarg :e-set
	   :documentation
	  "Mset of edges.  Each edge is a cons (from-v . to-v)."))
  (:documentation
  "A simple implementation of the strongly-conn functions.  Use the
interactive function input-strongly-conn-graph to create one."))

(defmethod strongly-conn-vertices ((g strongly-conn-graph))
  (slot-value g 'v-set))

(defmethod strongly-conn-num-vertices ((g strongly-conn-graph))
  (mset-size (slot-value g 'v-set)))

(defmethod strongly-conn-edges-from ((g strongly-conn-graph) v)
  (with-slots (e-set) g
    (mset-subset #'(lambda (e) (equalp v (car e))) e-set)))

(defmethod strongly-conn-ending-vertex ((g strongly-conn-graph) e)
  (cdr e))

(defun input-strongly-conn-graph ()
  "At the prompt, enter the directed edges as pairs of vertices.
Vertices must be non-null, and equalp must be an equality test on
vertices.  Enter nil to stop adding edges.  Returns the
strongly-conn-graph.  An example of a triangle oriented cyclically:
CL-USER: (input-strongly-conn-graph)
? 0 1
? 1 2
? 2 0
? nil
 #<SHEAFHOM2::STRONGLY-CONN-GRAPH @ #x214c435a>
CL-USER: (strongly-conn-scc * 0)
 ((0 1 2))
CL-USER:"
  (let ((v-hash (make-hash-table :test #'equalp))
	(e-list '()))
    (loop 
      (format t "~&? ")
      (let ((from-v (read)))
	(unless from-v
	  (return))
	(let ((to-v (read)))
	  (unless to-v
	    (return))
	  (put-with-equalp-key from-v v-hash)
	  (put-with-equalp-key to-v v-hash)
	  (push (cons from-v to-v) e-list))))
    (make-instance 'strongly-conn-graph
      :v-set (make-hash-set v-hash) :e-set (make-hash-set e-list))))

