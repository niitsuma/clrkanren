;;;; fd.lisp -- finite-domain constraints, ported from cKanren's fd.scm and
;;;; finite-domain.scm (vendor/rkanren in scm2cpp).
;;;;
;;;;     (run* (q)
;;;;       (fresh (x y)
;;;;         (infd x y (range 0 6))
;;;;         (timesfd x y 6)
;;;;         (== q `(,x ,y))))
;;;;     ;; => ((1 6) (2 3) (3 2) (6 1))
;;;;
;;;; A domain is a sorted list of non-negative integers.  Every variable an
;;;; fd constraint mentions must be given one with infd or domfd (or be
;;;; bound to a number) by the time the answer is reified; then the domains
;;;; left are enumerated.
;;;;
;;;; Differences from the Scheme, which scm2cpp's Racket build never
;;;; compiled: the <=fd-c bounds call copy-before and drop-before (the
;;;; source names copy-before-dom and drop-before-dom, defined nowhere),
;;;; =fd-c builds its oc with its own name rather than the goal =fd's,
;;;; R6RS div is floor, and force-ans stops at a variable it has already
;;;; entered, so a cyclic term can carry fd variables.

(in-package #:clrkanren)

;;; ------------------------------------------------------------ domains

(defun range (lb ub)
  "The domain LB .. UB; (LB) when UB is below LB, as in the original."
  (if (< lb ub)
      (loop for n from lb to ub collect n)
      (list lb)))

(defun value-dom? (v) (and (integerp v) (<= 0 v)))

;; n* should be a non-empty sorted (small to large) list of value-dom?s,
;; with no duplicates
(defun make-dom (n*) n*)

(defun null-dom? (x) (null x))
(defun singleton-dom? (dom) (null (cdr dom)))
(defun singleton-element-dom (dom) (car dom))
(defun min-dom (dom) (car dom))
(defun max-dom (dom) (car (last dom)))
(defun memv-dom? (v dom) (and (value-dom? v) (member v dom)))


;;; The merges below are loops rather than the original's recursion: a
;;; domain of (range 0 99999) would overflow the stack.

(defun intersection-dom (dom1 dom2)
  (let ((acc '()))
    (loop
      (cond
        ((or (null dom1) (null dom2)) (return (nreverse acc)))
        ((= (car dom1) (car dom2))
         (push (car dom1) acc)
         (setf dom1 (cdr dom1) dom2 (cdr dom2)))
        ((< (car dom1) (car dom2)) (setf dom1 (cdr dom1)))
        (t (setf dom2 (cdr dom2)))))))

(defun diff-dom (dom1 dom2)
  (let ((acc '()))
    (loop
      (cond
        ((or (null dom1) (null dom2)) (return (nreconc acc dom1)))
        ((= (car dom1) (car dom2)) (setf dom1 (cdr dom1) dom2 (cdr dom2)))
        ((< (car dom1) (car dom2)) (push (car dom1) acc) (setf dom1 (cdr dom1)))
        (t (setf dom2 (cdr dom2)))))))

(defun copy-before (pred dom)
  (loop for n in dom until (funcall pred n) collect n))

(defun drop-before (pred dom)
  (member-if pred dom))

(defun disjoint-dom? (dom1 dom2)
  (loop
    (cond
      ((or (null dom1) (null dom2)) (return t))
      ((= (car dom1) (car dom2)) (return nil))
      ((< (car dom1) (car dom2)) (setf dom1 (cdr dom1)))
      (t (setf dom2 (cdr dom2))))))

(defun map-sum (f)
  "A goal that tries F on each element of a list, one conde branch each."
  (labels ((lp (ls)
             (if (null ls)
                 (lambda (a) (declare (ignore a)) (mzero))
                 (conde
                   ((funcall f (car ls)))
                   ((lp (cdr ls)))))))
    #'lp))

;;; ------------------------------------------------------------ helpers

(defun list-sorted? (pred ls)
  (loop for (x y) on ls
        while y
        always (funcall pred x y)))

(defun list-insert (pred x ls)
  (cond
    ((null ls) (list x))
    ((funcall pred x (car ls)) (cons x ls))
    (t (cons (car ls) (list-insert pred x (cdr ls))))))

;;; ------------------------------------------------------------ the store

(defun pred_x (x)
  (lambda (oc)
    (and (eq (oc->rator oc) 'domfd-c)
         (eq (car (oc->rands oc)) x))))

(defun ext-d (x dom F)
  (let ((oc (build-oc domfd-c x dom))
        (pred (pred_x x)))
    (cons oc (if (find-if pred F) (remove-if pred F) F))))

;;; procedures below this point cannot expose the representation of doms

(defun get-dom (x F)
  (let ((oc (find-if (pred_x x) F)))
    (and oc (cadr (oc->rands oc)))))

(defun process-dom (v dom)
  (lambda (a)
    (cond
      ((var? v) (funcall (update-var-dom v dom) a))
      ((memv-dom? v dom) a)
      (t nil))))

(defun update-var-dom (x dom)
  (lambda (a)
    (let ((xdom (get-dom x (c->F a))))
      (if xdom
          (let ((i (intersection-dom xdom dom)))
            (if (null-dom? i)
                nil
                (funcall (resolve-storable-dom i x) a)))
          (funcall (resolve-storable-dom dom x) a)))))

(defun resolve-storable-dom (dom x)
  (lambda (a)
    (if (singleton-dom? dom)
        (funcall (update-s x (singleton-element-dom dom)) a)
        (update-F a (ext-d x dom (c->F a))))))

(defun force-ans (x &optional seen)
  "Enumerate the domains of the variables in X.  SEEN holds the variables
already entered, so that a cyclic term is gone through once."
  (lambda (a)
    (let ((v (walk x (c->S a))))
      (funcall
       (cond
         ((and (var? x) (memq x seen)) #'unit)
         ((and (var? v) (get-dom v (c->F a)))
          (funcall (map-sum (lambda (n) (update-s v n))) (get-dom v (c->F a))))
         ((consp v)
          (let ((seen (if (var? x) (cons x seen) seen)))
            (fresh ()
              (force-ans (car v) seen)
              (force-ans (cdr v) seen))))
         (t #'unit))
       a))))

(defmacro let-dom ((S F) bindings &body body)
  "(let-dom (S F) ((u d_u) ...) body): each u walked, and d_u its domain --
the one stored for a variable, the singleton for a value."
  `(let ,(loop for (u) in bindings collect `(,u (walk ,u ,S)))
     (let ,(loop for (u d) in bindings
                 collect `(,d (if (var? ,u) (get-dom ,u ,F) (make-dom (list ,u)))))
       ,@body)))

(defmacro c-op (op bindings body)
  "The m-proc of the constraint OP: stored as an oc, and when every operand
has a domain, BODY narrows them."
  (let ((a (gensym "A")) (S (gensym "S")) (F (gensym "F")) (oc (gensym "OC")))
    `(lambda (,a)
       (let ((,S (c->S ,a)) (,F (c->F ,a)))
         (let-dom (,S ,F) ,bindings
           (let ((,oc (build-oc ,op ,@(mapcar #'first bindings))))
             (if (and ,@(mapcar #'second bindings))
                 (funcall (composem (update-c ,oc) ,body) ,a)
                 (funcall (update-c ,oc) ,a))))))))

;;; ------------------------------------------------------------ constraints

(defun =/=fd-c (u v)
  (lambda (a)
    (let-dom ((c->S a) (c->F a)) ((u d_u) (v d_v))
      (cond
        ((or (not d_u) (not d_v))
         (funcall (update-c (build-oc =/=fd-c u v)) a))
        ((and (singleton-dom? d_u)
              (singleton-dom? d_v)
              (= (singleton-element-dom d_u) (singleton-element-dom d_v)))
         nil)
        ((disjoint-dom? d_u d_v) a)
        (t
         (let ((oc (build-oc =/=fd-c u v)))
           (cond
             ((singleton-dom? d_u)
              (funcall (composem (update-c oc) (process-dom v (diff-dom d_v d_u))) a))
             ((singleton-dom? d_v)
              (funcall (composem (update-c oc) (process-dom u (diff-dom d_u d_v))) a))
             (t (funcall (update-c oc) a)))))))))

(defun distinctfd-c (v*)
  (lambda (a)
    (let ((v* (walk v* (c->S a))))
      (if (var? v*)
          (funcall (update-c (build-oc distinctfd-c v*)) a)
          (let ((x* (remove-if-not #'var? v*))
                (n* (list-sort #'< (remove-if #'var? v*))))
            (if (list-sorted? #'< n*)
                (funcall (distinct/fd-c x* n*) a)
                nil))))))

(defun distinct/fd-c (y* n*)
  (lambda (a)
    ;; fresh bindings: the oc keeps this closure and may run it again
    (let ((S (c->S a)) (F (c->F a)) (y* y*) (n* n*) (x* '()))
      (loop
        (when (null y*)
          (let ((oc (build-oc distinct/fd-c x* n*)))
            (return (funcall (composem (update-c oc)
                                       (exclude-from-dom (make-dom n*) F x*))
                             a))))
        (let ((y (walk (car y*) S)))
          (cond
            ((var? y) (push y x*))
            ;; n* is NOT A DOM
            ((member y n*) (return nil))
            (t (setf n* (list-insert #'< y n*)))))
        (setf y* (cdr y*))))))

(defun exclude-from-dom (dom1 F x*)
  (cond
    ((null x*) #'identitym)
    ((get-dom (car x*) F)
     (composem (process-dom (car x*) (diff-dom (get-dom (car x*) F) dom1))
               (exclude-from-dom dom1 F (cdr x*))))
    (t (exclude-from-dom dom1 F (cdr x*)))))

(defun =fd-c (u v)
  (c-op =fd-c ((u d_u) (v d_v))
    (let ((i (intersection-dom d_u d_v)))
      (composem (process-dom u i) (process-dom v i)))))

(defun <=fd-c (u v)
  (c-op <=fd-c ((u d_u) (v d_v))
    (let ((umin (min-dom d_u))
          (vmax (max-dom d_v)))
      (composem
       (process-dom u (copy-before (lambda (n) (< vmax n)) d_u))
       (process-dom v (drop-before (lambda (n) (<= umin n)) d_v))))))

(defun plusfd-c (u v w)
  (c-op plusfd-c ((u d_u) (v d_v) (w d_w))
    (let ((wmin (min-dom d_w)) (wmax (max-dom d_w))
          (umin (min-dom d_u)) (umax (max-dom d_u))
          (vmin (min-dom d_v)) (vmax (max-dom d_v)))
      (composem
       (process-dom w (range (+ umin vmin) (+ umax vmax)))
       (composem
        (process-dom u (range (- wmin vmax) (- wmax vmin)))
        (process-dom v (range (- wmin umax) (- wmax umin))))))))

(defun timesfd-c (u v w)
  (flet ((safe-div (n c a) (if (zerop n) c (values (floor a n)))))
    (c-op timesfd-c ((u d_u) (v d_v) (w d_w))
      (let ((wmin (min-dom d_w)) (wmax (max-dom d_w))
            (umin (min-dom d_u)) (umax (max-dom d_u))
            (vmin (min-dom d_v)) (vmax (max-dom d_v)))
        (let ((u-range (range (safe-div vmax umin wmin) (safe-div vmin umax wmax)))
              (v-range (range (safe-div umax vmin wmin) (safe-div umin vmax wmax)))
              (w-range (range (* umin vmin) (* umax vmax))))
          (composem
           (process-dom w w-range)
           (composem
            (process-dom u u-range)
            (process-dom v v-range))))))))

;;; ------------------------------------------------------------ enforcement

(defun enforce-constraintsfd (x)
  (fresh ()
    (force-ans x)
    (lambda (a)
      (let* ((F (c->F a))
             (bound-x* (loop for oc in F
                             when (eq (oc->rator oc) 'domfd-c)
                               collect (car (oc->rands oc)))))
        (verify-all-bound (c->S a) F bound-x*)
        (funcall (onceo (force-ans bound-x*)) a)))))

(defun verify-all-bound (S F bound-x*)
  (dolist (oc F)
    (when (member (oc->rator oc)
                  '(=/=fd-c distinctfd-c distinct/fd-c <=fd-c =fd-c plusfd-c timesfd-c))
      (let ((x (find-if (lambda (x) (and (var? x) (not (memq x bound-x*))))
                        (oc->rands oc))))
        (when (and x (not (value-dom? (walk x S))))
          (error "verify-all-bound: constrained variable ~S without domain" x))))))

(extend-enforce-fns 'fd #'enforce-constraintsfd)

;;; ------------------------------------------------------------ goals

(defun domfd-c (x n*)
  (lambda (a)
    (funcall (process-dom (walk x (c->S a)) (make-dom n*)) a)))

(defun domfd (x n*) (goal-construct (domfd-c x n*)))

(defmacro infd (x0 &rest xs+e)
  "(infd x ... dom): each x in DOM."
  (let ((n* (gensym "N*")))
    `(let ((,n* ,(car (last xs+e))))
       (fresh () (domfd ,x0 ,n*) ,@(loop for x in (butlast xs+e) collect `(domfd ,x ,n*))))))

(defun =fd (u v) (goal-construct (=fd-c u v)))
(defun =/=fd (u v) (goal-construct (=/=fd-c u v)))
(defun <=fd (u v) (goal-construct (<=fd-c u v)))
(defun <fd (u v) (fresh () (<=fd u v) (=/=fd u v)))
(defun plusfd (u v w) (goal-construct (plusfd-c u v w)))
(defun timesfd (u v w) (goal-construct (timesfd-c u v w)))
(defun distinctfd (v*) (goal-construct (distinctfd-c v*)))
