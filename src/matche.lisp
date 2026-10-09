;;;; matche.lisp -- pattern matching over logic terms.
;;;;
;;;; The Scheme matche writes a pattern bare, (,a ,b), and quasiquotes it
;;;; itself.  A comma outside a backquote is a reader error in Common Lisp,
;;;; so here the pattern carries its own backquote:
;;;;
;;;;     (matche x
;;;;       (`(,a . ,d) (== a 1))
;;;;       (`(b ,c)    (== c 2))
;;;;       (`,w        (== w 3))      ; binds the whole
;;;;       ((5 6)      succeed))      ; no backquote: a literal
;;;;
;;;; Each unquoted symbol becomes a fresh variable for that clause, and a
;;;; symbol unquoted twice is the same variable.  Reading the unquoted
;;;; symbols out of a backquote form depends on how the reader represents
;;;; it, which the standard leaves open; this is SBCL's.

(in-package #:clrkanren)

(defun quasiquote-form-p (x)
  #+sbcl (and (consp x) (eq (car x) 'sb-int:quasiquote))
  #-sbcl (declare (ignore x))
  #-sbcl (error "matche reads backquoted patterns only under SBCL"))

(defun pattern-variables (pat)
  "The unquoted symbols of the backquote form PAT, first occurrence first."
  (let ((vars '()))
    (labels ((walk (x)
               (cond
                 #+sbcl
                 ((sb-impl::comma-p x)
                  (let ((e (sb-impl::comma-expr x)))
                    (unless (and (symbolp e) (zerop (sb-impl::comma-kind x)))
                      (error "matche: only ,symbol may appear in a pattern, not ~S" x))
                    (pushnew e vars)))
                 ((consp x) (walk (car x)) (walk (cdr x))))))
      (walk (second pat)))
    (nreverse vars)))

(defmacro matche (v &rest clauses)
  (let ((val (gensym "V")))
    `(let ((,val ,v))
       (conde
         ,@(loop for (pat . goals) in clauses
                 collect (if (quasiquote-form-p pat)
                             `((fresh ,(pattern-variables pat) (== ,pat ,val) ,@goals))
                             `((== ',pat ,val) ,@goals)))))))

(defmacro lambdae ((&rest xs) &body clauses)
  `(lambda ,xs (matche (list ,@xs) ,@clauses)))

;;; ------------------------------------------------------------ matchee
;;;
;;; matche with repetition, after Niitsuma's matchee: in a pattern,
;;; (h ___ . tail) matches a list whose prefix is any number of elements
;;; each matching h and whose rest matches tail.  A variable inside h
;;; stands for the list of what it matched in each element:
;;;
;;;     (run* (q)
;;;       (matchee '((1 (2 3)) (10 (2 30)) (100 (2 300)))
;;;         (`((,a (2 ,b)) ___) (== q `(,a ,b)))))
;;;     ;; => (((1 10 100) (3 30 300)))
;;;
;;; ___ is written where syntax-rules would write ..., which the reader
;;; keeps for itself.  The original rewrites the pattern with syntax
;;; computations (SRFI 53); here it is compiled directly.  Each (h ___ . t)
;;; becomes a variable W for the whole, with
;;;
;;;     (appendo P t W)                       P is the repeated prefix
;;;     (for-eache (lambda (e x ...) (== h e) ...) P x ...)
;;;
;;; where x ... are h's variables, so an ___ nested inside h repeats per
;;; element, as it should.

(defun ellipsis-p (x)
  (and (symbolp x) (string= (symbol-name x) "___")))

(defun compile-matchee-template (x)
  "Compile the inside of a backquoted pattern.  Returns a form building the
term, the user's variables (first occurrence first), the variables the
compilation introduced, and the goals that constrain them."
  (let ((user '()) (aux '()) (goals '()))
    (labels ((adjoin-user (v) (unless (member v user) (setf user (append user (list v)))))
             (walk (x)
               (cond
                 #+sbcl
                 ((sb-impl::comma-p x)
                  (let ((e (sb-impl::comma-expr x)))
                    (unless (and (symbolp e) (zerop (sb-impl::comma-kind x)))
                      (error "matchee: only ,symbol may appear in a pattern, not ~S" x))
                    (adjoin-user e)
                    e))
                 ((and (consp x) (consp (cdr x)) (ellipsis-p (cadr x)))
                  (multiple-value-bind (h-form h-user h-aux h-goals)
                      (compile-matchee-template (car x))
                    ;; the split comes before the tail's own goals: it is
                    ;; what the matched value grounds, and a tail holding
                    ;; another ___ would otherwise enumerate unbounded
                    (let* ((before goals)
                           (t-form (progn (setf goals '()) (walk (cddr x))))
                           (t-goals goals)
                           (prefix (gensym "PREFIX"))
                           (whole (gensym "WHOLE"))
                           (e (gensym "E")))
                      (mapc #'adjoin-user h-user)
                      (setf aux (append aux (list prefix whole)))
                      (setf goals
                            (append before
                                    `((appendo ,prefix ,t-form ,whole)
                                      (for-eache (lambda (,e ,@h-user)
                                                   (fresh ,h-aux (== ,h-form ,e) ,@h-goals))
                                                 ,prefix ,@h-user))
                                    t-goals))
                      whole)))
                 ((consp x)
                  (let ((a (walk (car x))))
                    `(cons ,a ,(walk (cdr x)))))
                 ((null x) nil)
                 (t `',x))))
      (let ((form (walk x)))
        (values form user aux goals)))))

(defmacro matchee (v &rest clauses)
  (let ((val (gensym "V")))
    `(let ((,val ,v))
       (conde
         ,@(loop for (pat . goals) in clauses
                 collect (if (quasiquote-form-p pat)
                             (multiple-value-bind (form user aux pgoals)
                                 (compile-matchee-template (second pat))
                               `((fresh (,@user ,@aux)
                                   (== ,form ,val) ,@pgoals ,@goals)))
                             `((== ',pat ,val) ,@goals)))))))
