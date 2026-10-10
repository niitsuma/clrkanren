;;;; ck.lisp -- the constraint framework of cKanren (Alvis, Byrd, Friedman,
;;;; Kiselyov, Willcock, Carter 2011), the part of its ck.scm that fd.lisp
;;;; needs, carried over onto the state of mk.lisp.
;;;;
;;;; cKanren's package a is (s . c); here it is the whole state, and its
;;;; constraint store c is the state's last field F.  A constraint is an
;;;; m-proc, a function from a state to a state or NIL.  Goals of mk.lisp
;;;; return the state itself for one answer and NIL for none, so an m-proc
;;;; is already a goal, and a goal of ==, which yields at most one answer,
;;;; is already an m-proc.

(in-package #:clrkanren)

(defun update-F (a F)
  "The state A with its fd store replaced by F."
  (destructuring-bind (B E S D Y N TT F0) a
    (declare (ignore F0))
    (list B E S D Y N TT F)))

;;; ------------------------------------------------------------ helpers

(defun any/var? (p)
  (cond
    ((var? p) t)
    ((consp p) (or (any/var? (car p)) (any/var? (cdr p))))
    (t nil)))

(defun any-relevant/var? (tm x*)
  (cond
    ((var? tm) (memq tm x*))
    ((consp tm) (or (any-relevant/var? (car tm) x*)
                    (any-relevant/var? (cdr tm) x*)))
    (t nil)))

(defun bound-vars (pfx)
  "The variables a substitution delta PFX touches: each one bound, and
each variable it was bound to, as cKanren's update-s wakes both."
  (let ((x* '()))
    (dolist (pr pfx x*)
      (pushnew (lhs pr) x*)
      (when (var? (rhs pr)) (pushnew (rhs pr) x*)))))

;;; ------------------------------------------------------------ m-procs

(defun identitym (a) a)

(defun composem (fm f^m)
  (lambda (a)
    (let ((a (funcall fm a)))
      (and a (funcall f^m a)))))

(defun goal-construct (fm)
  (lambda (a) (or (funcall fm a) (mzero))))

(defun update-s (x v)
  "Bind X to V as == does, so the other constraints are checked and the
fd constraints on X and V run again."
  (lambda (a) (funcall (== x v) a)))

;;; ------------------------------------------------------------ the store

;;; An oc (operator constraint) is (proc rator . rands): proc is the
;;; m-proc that enforces it, rator its name and rands what it constrains.
(defmacro build-oc (op &rest args)
  (let ((zs (loop repeat (length args) collect (gensym "Z"))))
    `(let ,(mapcar #'list zs args)
       (list* (,op ,@zs) ',op (list ,@zs)))))

(defun oc->proc (oc) (car oc))
(defun oc->rator (oc) (cadr oc))
(defun oc->rands (oc) (cddr oc))

(defun ext-c (oc F) (cons oc F))

(defun update-c (oc)
  "Keep OC in the store while something it constrains is still unbound."
  (lambda (a)
    (if (any/var? (oc->rands oc))
        (update-F a (ext-c oc (c->F a)))
        a)))

;;; ------------------------------------------------------------ fixed point

(defun run-constraints (x* F)
  "Rerun, each taken out of the store first, the constraints of F that
mention one of X*.  One that still has work left puts itself back."
  (cond
    ((null F) #'identitym)
    ((oc-relevant? (car F) x*)
     (composem (rem/run (car F)) (run-constraints x* (cdr F))))
    (t (run-constraints x* (cdr F)))))

(defun oc-relevant? (oc x*)
  ;; A domain oc is (x dom), and dom is integers only: searching it for
  ;; variables took most of the time on (range 0 99999).
  (if (eq (oc->rator oc) 'domfd-c)
      (memq (car (oc->rands oc)) x*)
      (any-relevant/var? (oc->rands oc) x*)))

(defun rem/run (oc)
  (lambda (a)
    (let ((F (c->F a)))
      (if (memq oc F)
          (funcall (oc->proc oc) (update-F a (remove oc F :test #'eq :count 1)))
          a))))

;;; ------------------------------------------------------------ enforcement

;;; Before an answer is reified, each kind of constraint may bind what it
;;; still holds open -- fd enumerates the domains left.  cKanren keeps the
;;; table in a parameter; here it is a special variable of (tag . fn).
(defvar *enforce-fns* '())

(defun extend-enforce-fns (tag fn)
  (unless (assoc tag *enforce-fns*)
    (setf *enforce-fns* (cons (cons tag fn) *enforce-fns*))))

(defun enforce-constraints (x)
  (lambda (a)
    (if (null (c->F a))
        (unit a)                        ; nothing held open: the common case
        (funcall (labels ((loop-fns (fns)
                            (if (null fns)
                                #'unit
                                (fresh () (funcall (cdar fns) x) (loop-fns (cdr fns))))))
                   (loop-fns *enforce-fns*))
                 a))))
