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
