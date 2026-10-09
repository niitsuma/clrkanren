;;;; mk.lisp -- recursive miniKanren, in Common Lisp.
;;;;
;;;; A port of vendor/mk-recursive/mk.scm from scm2cpp: William Byrd's
;;;; miniKanren (with =/=, symbolo, numbero, absento and eigen) whose
;;;; walk, walk* and unify carry the change after Niitsuma's recursive
;;;; miniKanren:
;;;;
;;;;     Hirotaka Niitsuma, Context-Free Grammars Including Left Recursion
;;;;     using Recursive miniKanren, Computacion y Sistemas 22(4), 2018.
;;;;     https://doi.org/10.13053/cys-22-4-3072
;;;;
;;;; Stock miniKanren refuses a self-referential binding: the occurs check
;;;; sees the variable inside the term it is being bound to and fails.  Here
;;;; the binding is taken, unification is equi-recursive, and walk* names
;;;; the recursion when it meets it, as (==> x t).
;;;;
;;;; The definitions follow the Scheme source one for one and keep its
;;;; names, so the two can be read side by side.  What differs is only what
;;;; Common Lisp makes differ:
;;;;
;;;;   - Goals are functions held in variables, so they are FUNCALLed.
;;;;   - The empty list and false are both NIL.  The places the Scheme
;;;;     source relies on '() being true are noted where they occur.
;;;;   - Racket's immutable hasheq beside the association list becomes a
;;;;     persistent hash trie keyed on a serial number each variable carries.
;;;;   - T cannot be a variable, so the constraint store's T is called TT.

(in-package #:clrkanren)

;;; ------------------------------------------------------------ Scheme shims

(defmacro define-goal-constant (name form)
  "Define NAME as a global goal value, read the way Scheme's (define NAME FORM)
is: as a plain variable that may be passed around and called."
  (let ((cell (intern (format nil "%~A-GOAL" (symbol-name name)))))
    `(progn
       (defvar ,cell)
       (setf ,cell ,form)
       (define-symbol-macro ,name ,cell))))

(declaim (inline memq))
(defun memq (x l) (member x l :test #'eq))

(defun scheme-symbol? (x)
  "Scheme's symbol?: NIL and T stand for '() and #t, which are not symbols."
  (and (symbolp x) x (not (eq x t))))

(defun scheme-equal? (a b)
  "Racket's equal? on the data a term can hold."
  (cond
    ((and (consp a) (consp b))
     (and (scheme-equal? (car a) (car b))
          (scheme-equal? (cdr a) (cdr b))))
    ((and (stringp a) (stringp b)) (string= a b))
    ((and (vectorp a) (vectorp b) (not (stringp a)) (not (stringp b)))
     (and (= (length a) (length b))
          (every #'scheme-equal? a b)))
    (t (eql a b))))

(defun remp (p ls) (remove-if p ls))

(defun list-sort (pred ls)
  "Racket's sort: stable, on a fresh list."
  (stable-sort (copy-list ls) pred))

;;; ------------------------------------------------------------ variables

;; A variable carries a serial number for the substitution's hash to key on;
;; identity is still EQ.
(defvar *var-counter* 0)
(declaim (type fixnum *var-counter*))

(defstruct (lvar (:constructor %make-lvar (name id)) (:predicate lvar-p))
  name
  (id 0 :type fixnum :read-only t))

(defmethod print-object ((v lvar) stream)
  (if *print-readably*
      (call-next-method)
      (format stream "#<var ~A ~D>" (lvar-name v) (lvar-id v))))

(defstruct (eigen (:constructor eigen-var ()) (:predicate eigen-p)))

(defmethod print-object ((e eigen) stream)
  (print-unreadable-object (e stream :identity t)
    (write-string "eigen" stream)))

(declaim (inline var var? eigen?))
(defun var (dummy) (%make-lvar dummy (incf *var-counter*)))
(defun var? (x) (lvar-p x))
(defun eigen? (x) (eigen-p x))

(declaim (inline lhs rhs))
(defun rhs (pr) (cdr pr))
(defun lhs (pr) (car pr))

(defun datum->string (x)
  "Racket's display, which the reifier sorts by."
  (with-output-to-string (out)
    (labels ((d (x)
               (cond
                 ((null x) (write-string "()" out))
                 ((eq x t) (write-string "#t" out))
                 ((symbolp x)
                  (let ((n (symbol-name x)))
                    ;; the reader folded it to upper case; show it as written
                    (write-string (if (some #'lower-case-p n) n (string-downcase n))
                                  out)))
                 ((consp x)
                  (write-char #\( out)
                  (d (car x))
                  (loop for tail = (cdr x) then (cdr tail)
                        while (consp tail)
                        do (write-char #\Space out) (d (car tail))
                        finally (when tail
                                  (write-string " . " out)
                                  (d tail)))
                  (write-char #\) out))
                 ((lvar-p x) (write-string "#(" out) (d (lvar-name x)) (write-char #\) out))
                 ((eigen-p x) (write-string "#(#(eigen-tag))" out))
                 ((stringp x) (write-string x out))
                 ((characterp x) (write-char x out))
                 ((vectorp x)
                  (write-string "#(" out)
                  (loop for i from 0 below (length x)
                        do (when (plusp i) (write-char #\Space out))
                           (d (aref x i)))
                  (write-char #\) out))
                 (t (princ x out)))))
      (d x))))

;;; ------------------------------------------------------------ persistent map
;;;
;;; The substitution is a pair: the association list the rest of this file
;;; expects, and a map of the same bindings for walk to look in.  Walking was
;;; ninety-eight per cent of the time of a whole-program type inference, all
;;; of it in assq down a list of some thousands of bindings; the list is kept
;;; because prefix-S reads deltas off its tails.  The map is a hash trie on
;;; the variable's serial number, four bits a level, copied along its path on
;;; each extension, so every earlier substitution stays valid.

(defstruct (smap (:constructor %make-smap (root))) (root nil :read-only t))

(defun smap-ref (m key)
  "The binding of KEY in M as (KEY . VALUE), or NIL."
  (let ((node (smap-root m))
        (id (lvar-id key)))
    (declare (type fixnum id))
    (loop
      (cond
        ((null node) (return nil))
        ((consp node) (return (if (eq (car node) key) node nil)))
        (t (setf node (svref node (logand id 15))
                 id (ash id -4)))))))

(defun trie-set (node key val id-rest other-shift)
  (declare (type fixnum id-rest other-shift))
  (cond
    ((null node) (cons key val))
    ((consp node)
     (if (eq (car node) key)
         (cons key val)
         (let ((v (make-array 16 :initial-element nil)))
           (setf (svref v (ldb (byte 4 other-shift) (lvar-id (car node)))) node)
           (trie-set v key val id-rest other-shift))))
    (t
     (let ((v (copy-seq node))
           (i (logand id-rest 15)))
       (setf (svref v i)
             (trie-set (svref node i) key val (ash id-rest -4) (+ other-shift 4)))
       v))))

(defun smap-set (m key val)
  (%make-smap (trie-set (smap-root m) key val (lvar-id key) 0)))

(defvar +empty-smap+ (%make-smap nil))

;;; ------------------------------------------------------------ substitution

(defun s-empty () (cons '() +empty-smap+))
(declaim (inline s-hashed?))
(defun s-hashed? (S) (and (consp S) (smap-p (cdr S))))
(defun s-ref (S u)
  (if (s-hashed? S)
      (smap-ref (cdr S) u)
      (assoc u S :test #'eq)))
(defun s-ext (S x v)
  (if (s-hashed? S)
      (cons (cons (cons x v) (car S)) (smap-set (cdr S) x v))
      (cons (cons x v) S)))
(defun s-alist (S) (if (s-hashed? S) (car S) S))

(defun empty-c () (list '() '() (s-empty) '() '() '() '()))

(defun c->B (c) (first c))
(defun c->E (c) (second c))
(defun c->S (c) (third c))
(defun c->D (c) (fourth c))
(defun c->Y (c) (fifth c))
(defun c->N (c) (sixth c))
(defun c->T (c) (seventh c))

;;; ------------------------------------------------------------ streams

(defmacro lambdaf@ (() &body e) `(lambda () ,@e))
(defmacro inc (e) `(lambdaf@ () ,e))

(defmacro lambdag@ ((c &rest fields) &body e)
  "(lambdag@ (c) e) or (lambdag@ (c B E S) e) or (lambdag@ (c B E S D Y N T) e).
The Scheme form's ':' after c may be written |:| or left out."
  (let ((fields (if (and fields (string= (symbol-name (first fields)) ":"))
                    (rest fields)
                    fields)))
    (if (null fields)
        `(lambda (,c) ,@e)
        `(lambda (,c)
           (declare (ignorable ,c))
           (let ,(loop for f in fields
                       for acc in '(c->B c->E c->S c->D c->Y c->N c->T)
                       collect `(,f (,acc ,c)))
             (declare (ignorable ,@fields))
             ,@e)))))

(declaim (inline mzero unit choice))
(defun mzero () nil)
(defun unit (c) c)
(defun choice (c f) (cons c f))

(defmacro case-inf (e (() &body e0) ((f^) &body e1) ((c^) &body e2) ((c f) &body e3))
  (let ((c-inf (gensym "C-INF")))
    `(let ((,c-inf ,e))
       (cond
         ((not ,c-inf) ,@e0)
         ((functionp ,c-inf) (let ((,f^ ,c-inf)) (declare (ignorable ,f^)) ,@e1))
         ((not (and (consp ,c-inf) (functionp (cdr ,c-inf))))
          (let ((,c^ ,c-inf)) (declare (ignorable ,c^)) ,@e2))
         (t (let ((,c (car ,c-inf)) (,f (cdr ,c-inf)))
              (declare (ignorable ,c ,f))
              ,@e3))))))

(defun empty-f () (mzero))

(defun mplus (c-inf f)
  (case-inf c-inf
    (() (funcall f))
    ((f^) (inc (mplus (funcall f) f^)))
    ((c) (choice c f))
    ((c f^) (choice c (lambdaf@ () (mplus (funcall f) f^))))))

(defun bind (c-inf g)
  (case-inf c-inf
    (() (mzero))
    ((f) (inc (bind (funcall f) g)))
    ((c) (funcall g c))
    ((c f) (mplus (funcall g c) (lambdaf@ () (bind (funcall f) g))))))

(defmacro bind* (e &rest gs)
  (if (null gs) e `(bind* (bind ,e ,(first gs)) ,@(rest gs))))

(defmacro mplus* (e &rest es)
  (if (null es) e `(mplus ,e (lambdaf@ () (mplus* ,@es)))))

(defun take_ (n f)
  "Up to N answers (all of them when N is NIL) from the stream thunk F."
  (let ((acc '()))
    (loop
      (when (and n (zerop n)) (return (nreverse acc)))
      (case-inf (funcall f)
        (() (return (nreverse acc)))
        ((f^) (setf f f^))
        ((c) (return (nreverse (cons c acc))))
        ((c f^) (push c acc)
                (setf f f^
                      n (and n (- n 1))))))))

;;; ------------------------------------------------------------ goal syntax

(defmacro fresh ((&rest xs) g0 &rest gs)
  (let ((c (gensym "C")))
    `(lambda (,c)
       (inc
        (let ,(loop for x in xs collect `(,x (var ',x)))
          (let ((,c (if ',xs
                        (cons (append (list ,@xs) (c->B ,c)) (cdr ,c))
                        ,c)))
            (bind* (funcall ,g0 ,c) ,@gs)))))))

(defmacro eigen ((&rest xs) g0 &rest gs)
  (let ((c (gensym "C")))
    `(lambda (,c)
       (let ,(loop for x in xs collect `(,x (eigen-var)))
         (funcall (fresh () (eigen-absento (list ,@xs) (c->B ,c)) ,g0 ,@gs) ,c)))))

(defmacro conde (&rest clauses)
  (let ((c (gensym "C")))
    `(lambda (,c)
       (inc
        (mplus* ,@(loop for (g0 . gs) in clauses
                        collect `(bind* (funcall ,g0 ,c) ,@gs)))))))

(defmacro ifa (&rest clauses)
  (if (null clauses)
      '(mzero)
      (destructuring-bind ((e &rest gs) &rest more) clauses
        ;; the clause's goals are spliced inside case-inf's bindings, so
        ;; those are gensyms: a user's variable named a or f stays theirs
        (let ((loop (gensym "LOOP")) (c-inf (gensym "C-INF"))
              (a (gensym "A")) (f (gensym "F")))
          `(labels ((,loop (,c-inf)
                      (case-inf ,c-inf
                        (() (ifa ,@more))
                        ((,f) (inc (,loop (funcall ,f))))
                        ((,a) (bind* ,c-inf ,@gs))
                        ((,a ,f) (bind* ,c-inf ,@gs)))))
             (,loop ,e))))))

(defmacro ifu (&rest clauses)
  (if (null clauses)
      '(mzero)
      (destructuring-bind ((e &rest gs) &rest more) clauses
        (let ((loop (gensym "LOOP")) (c-inf (gensym "C-INF"))
              (c (gensym "C")) (f (gensym "F")))
          `(labels ((,loop (,c-inf)
                      (case-inf ,c-inf
                        (() (ifu ,@more))
                        ((,f) (inc (,loop (funcall ,f))))
                        ((,c) (bind* ,c-inf ,@gs))
                        ((,c ,f) (bind* (unit ,c) ,@gs)))))
             (,loop ,e))))))

(defmacro conda (&rest clauses)
  (let ((c (gensym "C")))
    `(lambda (,c)
       (inc (ifa ,@(loop for (g0 . gs) in clauses
                         collect `((funcall ,g0 ,c) ,@gs)))))))

(defmacro condu (&rest clauses)
  (let ((c (gensym "C")))
    `(lambda (,c)
       (inc (ifu ,@(loop for (g0 . gs) in clauses
                         collect `((funcall ,g0 ,c) ,@gs)))))))

(defun onceo (g) (condu (g)))

(defmacro project ((&rest xs) g &rest gs)
  (let ((c (gensym "C")) (s (gensym "S")))
    `(lambda (,c)
       (let* ((,s (c->S ,c))
              ,@(loop for x in xs collect `(,x (walk* ,x ,s))))
         (funcall (fresh () ,g ,@gs) ,c)))))

(defmacro run (n (q0 &rest qs) g0 &rest gs)
  (if qs
      (let ((x (gensym "X")))
        `(run ,n (,x) (fresh (,q0 ,@qs) ,g0 ,@gs (== (list ,q0 ,@qs) ,x))))
      (let ((final-c (gensym "FINAL-C")))
        `(take_ ,n
                (lambdaf@ ()
                  (funcall (fresh (,q0) ,g0 ,@gs
                             (lambda (,final-c)
                               (choice (funcall (reify ,q0) ,final-c) #'empty-f)))
                           (empty-c)))))))

(defmacro run* ((&rest qs) g0 &rest gs)
  `(run nil ,qs ,g0 ,@gs))

(macrolet ((define-runs ()
             `(progn
                ,@(loop for i from 1 to 40
                        collect `(defmacro ,(intern (format nil "RUN~D" i)) (qs g0 &rest gs)
                                   (list* 'run ,i qs g0 gs))))))
  (define-runs))

;;; ------------------------------------------------------------ walk and unify

;; Bindings may be self-referential now, written (==> x t) after
;; Niitsuma's recursive miniKanren, so every traversal carries the
;; variables it has already entered.
(defun recursive-representation? (l)
  (if (and (consp l) (eq (car l) '==>) (consp (cdr l)) (var? (cadr l)))
      (cadr l)
      nil))
(defun make-recursive-representation (x tm) (list '==> x tm))

(defun walk (u S)
  (let ((seen '()))
    (loop
      (let ((pr (and (var? u) (not (memq u seen)) (s-ref S u))))
        (if pr
            (progn (push u seen) (setf u (rhs pr)))
            (return u))))))

(defun prefix-S (S+ S)
  (let ((stop (s-alist S)))
    (loop for l on (s-alist S+)
          until (eq l stop)
          collect (car l))))

;; seen holds pairs of term NODES compared by identity, not by equal:
;; a cyclic term has finitely many cells and revisits them, so the
;; identity check terminates where structural comparison on a cycle
;; would not.
(defun seen-pair? (u v seen)
  (loop for pr in seen
        thereis (and (eq (car pr) u) (eq (cdr pr) v))))

;; Equi-recursive unification: two terms are the same if their infinite
;; unrollings are, so an (==> x t) annotation is transparent -- unify
;; against t, with x's own binding holding the knot -- and a pair of
;; recursions already being compared is taken as equal rather than
;; unrolled again, which is the coinductive reading and what makes this
;; terminate.
;;
;; Failure is NIL.  A substitution built by run is never NIL, so the
;; conflation with '() only matters for the reifier's plain association
;; lists, which are never empty where they are unified against.
(defun unify (u v s)
  (unify/seen u v s '()))

(defun unify/seen (u v s seen)
  (let ((u (walk u s))
        (v (walk v s)))
    (cond
      ((eq u v) s)
      ((seen-pair? u v seen) s)
      ((var? u) (ext-s-check u v s))
      ((var? v) (ext-s-check v u s))
      ((recursive-representation? u)
       (unify/seen (caddr u) v s (cons (cons u v) seen)))
      ((recursive-representation? v)
       (unify/seen u (caddr v) s (cons (cons u v) seen)))
      ;; the pair now under comparison joins seen before its parts are
      ;; compared: with raw cyclic terms this is the only place the
      ;; cycle closes
      ((and (consp u) (consp v))
       (let* ((seen (cons (cons u v) seen))
              (s (unify/seen (car u) (car v) s seen)))
         (and s (unify/seen (cdr u) (cdr v) s seen))))
      ((or (eigen? u) (eigen? v)) nil)
      ((scheme-equal? u v) s)
      (t nil))))

(defun occurs-check (x v s)
  "Whether X occurs in V under S, entering each recursion once."
  (labels ((oc (v seen)
             (let ((v (walk v s)))
               (cond
                 ((var? v) (eq v x))
                 ((recursive-representation? v)
                  (let ((u (recursive-representation? v)))
                    (and (not (memq u seen))
                         (oc (caddr v) (cons u seen)))))
                 ((consp v) (or (oc (car v) seen) (oc (cdr v) seen)))
                 (t nil)))))
    (oc v '())))

(defun eigen-occurs-check (e* x s)
  (let ((x (walk x s)))
    (cond
      ((var? x) nil)
      ((eigen? x) (memq x e*))
      ((consp x)
       (or (eigen-occurs-check e* (car x) s)
           (eigen-occurs-check e* (cdr x) s)))
      (t nil))))

;; Where miniKanren refuses a self-referential binding, take it.  Bindings
;; extend unchecked; cycles are found by walk* when a term is actually
;; reified, and unify's seen-pairs make comparison terminate either way.
(defun ext-s-check (x v s)
  (s-ext s x v))

(defun unify* (S+ S)
  (unify (mapcar #'lhs S+) (mapcar #'rhs S+) S))

;; walk* is where a raw cycle is discovered: it tracks the chain of
;; variables it is inside, and a variable met again on its own path is
;; the knot -- the binding is wrapped (==> x t) at read time, and only
;; when the knot was actually met.  Annotations already in a term (a
;; reified answer walked against the namer, say) print through the same
;; ==> clause, the naming pass being the one whose walk yields symbols.
(defun walk* (v S)
  (let ((hits (make-hash-table :test 'eq)))
    (labels ((w* (v path)
               (cond
                 ;; the knot is found before walking: a variable already on
                 ;; its own path names the recursion
                 ((and (var? v) (memq v path))
                  (setf (gethash v hits) t)
                  ;; under the reifier's naming pass the knot mention
                  ;; prints as its name, the same one the ==> binder shows
                  (let ((n (walk v S)))
                    (if (scheme-symbol? n) n v)))
                 (t
                  (let ((w (if (var? v) (walk v S) v)))
                    (cond
                      ((var? w) w)
                      ((recursive-representation? w)
                       (let* ((x (recursive-representation? w))
                              (n (walk x S))
                              (x^ (if (scheme-symbol? n) n x)))
                         (if (memq x path)
                             x^
                             (list '==> x^ (w* (caddr w) (cons x path))))))
                      ((consp w)
                       (let* ((self (and (var? v) v))
                              (path (if self (cons self path) path))
                              (r (cons (w* (car w) path) (w* (cdr w) path))))
                         (if (and self (gethash self hits))
                             (progn (remhash self hits)
                                    (make-recursive-representation self r))
                             r)))
                      (t w)))))))
      (w* v '()))))

;;; ------------------------------------------------------------ reification

(defvar *reify-package* nil
  "Package the reified names _.0, _.1, ... are interned in; NIL means
*PACKAGE* at the time of reification.")

(defun reify-name (n)
  (intern (format nil "_.~D" n) (or *reify-package* *package*)))

(defun reify-S (v S)
  (let ((v (walk v S)))
    (cond
      ((var? v) (cons (cons v (reify-name (length S))) S))
      ((consp v) (reify-S (cdr v) (reify-S (car v) S)))
      (t S))))

(defun drop-dot (X)
  (mapcar (lambda (tm) (list (lhs tm) (rhs tm))) X))

(defun lex<=? (x y)
  (string<= (datum->string x) (datum->string y)))

(defun lex<? (x y)
  (string< (datum->string x) (datum->string y)))

(defun sorter (ls)
  (list-sort #'lex<? ls))

(defun anyvar? (u r)
  (if (consp u)
      (or (anyvar? (car u) r) (anyvar? (cdr u) r))
      (var? (walk u r))))

(defun anyeigen? (u r)
  (if (consp u)
      (or (anyeigen? (car u) r) (anyeigen? (cdr u) r))
      (eigen? (walk u r))))

(defun member* (u v)
  (cond
    ((scheme-equal? u v) t)
    ((consp v) (or (member* u (car v)) (member* u (cdr v))))
    (t nil)))

;;; ------------------------------------------------------------ constraint store

(defun remq1 (elem ls)
  (cond
    ((null ls) '())
    ((eq (car ls) elem) (cdr ls))
    (t (cons (car ls) (remq1 elem (cdr ls))))))

(defun tagged? (S Y y^)
  (some (lambda (y) (eql (walk y S) y^)) Y))

(defun untyped-var? (S Y N t^)
  (flet ((in-type? (y) (eq (walk y S) t^)))
    (and (var? t^)
         (notany #'in-type? Y)
         (notany #'in-type? N))))

(defun drop-N-b/c-const (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (find-if (lambda (n) (not (var? (walk n S)))) N)))
      (if hit (list B E S D Y (remq1 hit N) TT) c))))

(defun drop-Y-b/c-const (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (find-if (lambda (y) (not (var? (walk y S)))) Y)))
      (if hit (list B E S D (remq1 hit Y) N TT) c))))

(defun same-var? (v)
  (lambda (v^) (and (var? v) (var? v^) (eq v v^))))

(defun find-dup (f S)
  (lambda (elems)
    (loop for set^ on elems
          for elem = (car set^)
          for elem^ = (walk elem S)
          when (find-if (lambda (elem^^) (funcall (funcall f elem^) (walk elem^^ S)))
                        (cdr set^))
            return elem)))

(defun drop-N-b/c-dup-var (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (funcall (find-dup #'same-var? S) N)))
      (if hit (list B E S D Y (remq1 hit N) TT) c))))

(defun drop-Y-b/c-dup-var (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (funcall (find-dup #'same-var? S) Y)))
      (if hit (list B E S D (remq1 hit Y) N TT) c))))

(defun var-type-mismatch? (S Y N t1^ t2^)
  (cond
    ((num? S N t1^) (not (num? S N t2^)))
    ((sym? S Y t1^) (not (sym? S Y t2^)))
    (t nil)))

(defun term-ununifiable? (S Y N t1 t2)
  (let ((t1^ (walk t1 S))
        (t2^ (walk t2 S)))
    (cond
      ((or (untyped-var? S Y N t1^) (untyped-var? S Y N t2^)) nil)
      ((var? t1^) (var-type-mismatch? S Y N t1^ t2^))
      ((var? t2^) (var-type-mismatch? S Y N t2^ t1^))
      ((and (consp t1^) (consp t2^))
       (or (term-ununifiable? S Y N (car t1^) (car t2^))
           (term-ununifiable? S Y N (cdr t1^) (cdr t2^))))
      (t (not (eql t1^ t2^))))))

(defun T-term-ununifiable? (S Y N)
  (lambda (t1)
    (let ((t1^ (walk t1 S)))
      (labels ((t2-check (t2)
                 (let ((t2^ (walk t2 S)))
                   (if (consp t2^)
                       (and (term-ununifiable? S Y N t1^ t2^)
                            (t2-check (car t2^))
                            (t2-check (cdr t2^)))
                       (term-ununifiable? S Y N t1^ t2^)))))
        #'t2-check))))

(defun num? (S N u)
  (let ((u (walk u S)))
    (if (var? u) (tagged? S N u) (numberp u))))

(defun sym? (S Y u)
  (let ((u (walk u S)))
    (if (var? u) (tagged? S Y u) (scheme-symbol? u))))

(defun drop-T-b/c-Y-and-N (c)
  (destructuring-bind (B E S D Y N TT) c
    (let* ((drop-t? (T-term-ununifiable? S Y N))
           (tm (find-if (lambda (tm) (funcall (funcall drop-t? (lhs tm)) (rhs tm))) TT)))
      (if tm (list B E S D Y N (remq1 tm TT)) c))))

(defun move-T-to-D-b/c-t2-atom (c)
  (destructuring-bind (B E S D Y N TT) c
    (or (some (lambda (tm)
                (let ((t2^ (walk (rhs tm) S)))
                  (if (and (not (untyped-var? S Y N t2^))
                           (not (consp t2^)))
                      (list B E S (cons (list tm) D) Y N (remq1 tm TT))
                      nil)))
              TT)
        c)))

(defun term=? (u tm S)
  (let ((S0 (unify u tm S)))
    (and S0 (eq S0 S))))

(defun terms-pairwise=? (pr-a^ pr-d^ t-a^ t-d^ S)
  (or (and (term=? pr-a^ t-a^ S)
           (term=? pr-d^ t-a^ S))
      (and (term=? pr-a^ t-d^ S)
           (term=? pr-d^ t-a^ S))))

(defun T-superfluous-pr? (S Y N TT)
  (lambda (pr)
    (let ((pr-a^ (walk (lhs pr) S))
          (pr-d^ (walk (rhs pr) S)))
      (cond
        ((some (lambda (tm)
                 (terms-pairwise=? pr-a^ pr-d^ (walk (lhs tm) S) (walk (rhs tm) S) S))
               TT)
         ;; The Scheme source has (for-all p l) from its compat layer, which
         ;; is (and (map p l)) and so always true; kept as it behaves.
         (mapc (lambda (tm)
                 (let ((t-a^ (walk (lhs tm) S))
                       (t-d^ (walk (rhs tm) S)))
                   (or (not (terms-pairwise=? pr-a^ pr-d^ t-a^ t-d^ S))
                       (untyped-var? S Y N t-d^)
                       (consp t-d^))))
               TT)
         t)
        (t nil)))))

(defun drop-from-D-b/c-T (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (find-if (lambda (d) (some (T-superfluous-pr? S Y N TT) d)) D)))
      (if hit (list B E S (remq1 hit D) Y N TT) c))))

(defun mem-check (u tm S)
  (let ((tm (walk tm S)))
    (if (consp tm)
        (or (term=? u tm S)
            (mem-check u (car tm) S)
            (mem-check u (cdr tm) S))
        (term=? u tm S))))

(defun drop-t-b/c-t2-occurs-t1 (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((tm (find-if (lambda (tm)
                         (mem-check (walk (rhs tm) S) (walk (lhs tm) S) S))
                       TT)))
      (if tm (list B E S D Y N (remq1 tm TT)) c))))

(defun split-t-move-to-d-b/c-pair (c)
  (destructuring-bind (B E S D Y N TT) c
    (or (some (lambda (tm)
                (let ((t2^ (walk (rhs tm) S)))
                  (if (consp t2^)
                      (let ((ta (cons (lhs tm) (car t2^)))
                            (td (cons (lhs tm) (cdr t2^))))
                        (list B E S (cons (list tm) D) Y N
                              (list* ta td (remq1 tm TT))))
                      nil)))
              TT)
        c)))

(defun find-d-conflict (S Y N)
  (lambda (D)
    (find-if (lambda (d)
               (some (lambda (pr) (term-ununifiable? S Y N (lhs pr) (rhs pr))) d))
             D)))

(defun drop-D-b/c-Y-or-N (c)
  (destructuring-bind (B E S D Y N TT) c
    (let ((hit (funcall (find-d-conflict S Y N) D)))
      (if hit (list B E S (remq1 hit D) Y N TT) c))))

(defun LOF ()
  (list #'drop-N-b/c-const #'drop-Y-b/c-const #'drop-Y-b/c-dup-var
        #'drop-N-b/c-dup-var #'drop-D-b/c-Y-or-N #'drop-T-b/c-Y-and-N
        #'move-T-to-D-b/c-t2-atom #'split-t-move-to-d-b/c-pair
        #'drop-from-D-b/c-T #'drop-t-b/c-t2-occurs-t1))

(defun cycle (c)
  (let* ((fns (LOF))
         (len (length fns)))
    (loop with c^ = c
          with fns^ = fns
          with n = len
          do (cond
               ((zerop n) (return c^))
               ((null fns^) (setf fns^ fns))
               (t (let ((c^^ (funcall (car fns^) c^)))
                    (if (not (eq c^^ c^))
                        (setf c^ c^^ fns^ (cdr fns^) n len)
                        (setf fns^ (cdr fns^) n (- n 1)))))))))

;;; ------------------------------------------------------------ goals

(defun absento (u v)
  (lambdag@ (c B E S D Y N TT)
    (if (mem-check u v S)
        (mzero)
        (unit (list B E S D Y N (cons (cons u v) TT))))))

(defun eigen-absento (e* x*)
  (lambdag@ (c B E S D Y N TT)
    (if (eigen-occurs-check e* x* S)
        (mzero)
        (unit (list B (cons (cons e* x*) E) S D Y N TT)))))

(defun ground-non-<type>? (pred)
  (lambda (u S)
    (let ((u (walk u S)))
      (if (var? u) nil (not (funcall pred u))))))

(defvar ground-non-symbol? (ground-non-<type>? #'scheme-symbol?))
(defvar ground-non-number? (ground-non-<type>? #'numberp))

(defun symbolo (u)
  (lambdag@ (c B E S D Y N TT)
    (cond
      ((funcall ground-non-symbol? u S) (mzero))
      ((mem-check u N S) (mzero))
      (t (unit (list B E S D (cons u Y) N TT))))))

(defun numbero (u)
  (lambdag@ (c B E S D Y N TT)
    (cond
      ((funcall ground-non-number? u S) (mzero))
      ((mem-check u Y S) (mzero))
      (t (unit (list B E S D Y (cons u N) TT))))))

(defun =/= (u v)
  (lambdag@ (c B E S D Y N TT)
    (let ((S0 (unify u v S)))
      (if S0
          (let ((pfx (prefix-S S0 S)))
            (if (null pfx)
                (mzero)
                (unit (list B E S (cons pfx D) Y N TT))))
          c))))

(defun == (u v)
  (lambdag@ (c B E S D Y N TT)
    (let ((S0 (unify u v S)))
      (cond
        ((null S0) (mzero))
        ((==fail-check B E S0 D Y N TT) (mzero))
        (t (unit (list B E S0 D Y N TT)))))))

(define-goal-constant succeed (== nil nil))
(define-goal-constant fail (== nil t))

(defun ==fail-check (B E S0 D Y N TT)
  (declare (ignore B))
  (or (eigen-absento-fail-check E S0)
      (atomic-fail-check S0 Y ground-non-symbol?)
      (atomic-fail-check S0 N ground-non-number?)
      (symbolo-numbero-fail-check S0 Y N)
      (=/=-fail-check S0 D)
      (absento-fail-check S0 TT)))

(defun eigen-absento-fail-check (E S0)
  (some (lambda (e*/x*) (eigen-occurs-check (car e*/x*) (cdr e*/x*) S0)) E))

(defun atomic-fail-check (S A pred)
  (some (lambda (a) (funcall pred (walk a S) S)) A))

(defun symbolo-numbero-fail-check (S A N)
  (let ((N (mapcar (lambda (n) (walk n S)) N)))
    (some (lambda (a) (some (same-var? (walk a S)) N)) A)))

(defun absento-fail-check (S TT)
  (some (lambda (tm) (mem-check (lhs tm) (rhs tm) S)) TT))

(defun =/=-fail-check (S D)
  (some (d-fail-check S) D))

(defun d-fail-check (S)
  (lambda (d)
    (let ((S+ (unify* d S)))
      (and S+ (eq S+ S)))))

;;; ------------------------------------------------------------ reify

(defun reify (x)
  (lambda (c)
    (let* ((c (cycle c))
           (S (c->S c))
           (Y (walk* (c->Y c) S))
           (N (walk* (c->N c) S))
           (TT (walk* (c->T c) S))
           (v (walk* x S))
           (R (reify-S v '())))
      (reify+ v R
              (rem-subsumed
               (remp (lambda (d)
                       (let ((dw (walk* d S)))
                         (or (anyvar? dw R) (anyeigen? dw R))))
                     (rem-xx-from-d c)))
              (remp (lambda (y) (var? (walk y R))) Y)
              (remp (lambda (n) (var? (walk n R))) N)
              (remp (lambda (tm) (or (anyeigen? tm R) (anyvar? tm R))) TT)))))

(defun reify+ (v R D Y N TT)
  (form (walk* v R)
        (walk* D R)
        (walk* Y R)
        (walk* N R)
        (rem-subsumed-T (walk* TT R))))

(defun form (v D Y N TT)
  (let ((fd (sort-DD D))
        (fy (sorter Y))
        (fn (sorter N))
        (ft (sorter TT)))
    (let ((fd (if (null fd) fd (list (cons '=/= (drop-dot-D fd)))))
          (fy (if (null fy) fy (list (cons 'sym fy))))
          (fn (if (null fn) fn (list (cons 'num fn))))
          (ft (if (null ft) ft (list (cons 'absento (drop-dot ft))))))
      (if (and (null fd) (null fy) (null fn) (null ft))
          v
          (append (list v) fd fn fy ft)))))

(defun sort-DD (D)
  (sorter (mapcar #'sort-d D)))

(defun sort-d (d)
  (list-sort (lambda (x y) (lex<? (car x) (car y)))
             (mapcar #'sort-pr d)))

(defun drop-dot-D (D)
  (mapcar #'drop-dot D))

(defun lex<-reified-name? (r)
  (let ((s (datum->string r)))
    (and (plusp (length s)) (char< (char s 0) #\_))))

(defun sort-pr (pr)
  (let ((l (lhs pr))
        (r (rhs pr)))
    (cond
      ((lex<-reified-name? r) pr)
      ((lex<=? r l) (cons r l))
      (t pr))))

(defun rem-subsumed (D)
  ;; (Common Lisp folds case, so D and d are one symbol: the element is dd.)
  (loop with d^* = '()
        for tail on D
        for dd = (car tail)
        unless (or (subsumed? dd (cdr tail)) (subsumed? dd d^*))
          do (push dd d^*)
        finally (return d^*)))

(defun subsumed? (d d*)
  (loop for d^ in d*
        thereis (let ((u (unify* d^ d)))
                  (and u (eq u d)))))

(defun rem-xx-from-d (c)
  (destructuring-bind (B E S D Y N TT) c
    ;; a prefix may be '(), which Scheme keeps (it is true there); the
    ;; failures are told apart with a marker instead of NIL
    (remove :drop
            (mapcar (lambda (d)
                      (let ((S0 (unify* d S)))
                        (cond
                          ((null S0) :drop)
                          ((==fail-check B E S0 '() Y N TT) :drop)
                          (t (prefix-S S0 S)))))
                    (walk* D S)))))

(defun rem-subsumed-T (TT)
  (loop with T^ = '()
        for rest on TT
        for lit = (lhs (car rest))
        for big = (rhs (car rest))
        unless (or (subsumed-T? lit big (cdr rest)) (subsumed-T? lit big T^))
          do (push (car rest) T^)
        finally (return T^)))

(defun subsumed-T? (lit big TT)
  (loop for pr in TT
        thereis (and (eq big (rhs pr)) (member* (lhs pr) lit))))
