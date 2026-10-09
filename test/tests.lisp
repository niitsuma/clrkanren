;;;; tests.lisp -- the Common Lisp port checked against the Racket original,
;;;; and the parts that exist only here.

(defpackage #:clrkanren-test
  (:use #:common-lisp #:clrkanren)
  (:export #:run-tests))

(in-package #:clrkanren-test)

(defvar *failures* 0)
(defvar *checks* 0)

(defun report (label got want)
  (incf *checks*)
  (unless (equal got want)
    (incf *failures*)
    (format t "~&FAIL ~A~%  got  ~S~%  want ~S~%" label got want)))

(defmacro check (label form want)
  `(report ,label
           (handler-case ,form
             (error (e) (list :error (princ-to-string e))))
           ,want))

(defun test-file (name)
  (asdf:system-relative-pathname "clrkanren" (concatenate 'string "test/" name)))

(defun read-all (path)
  (with-open-file (in path :external-format :utf-8)
    (loop for f = (read in nil in)
          until (eq f in)
          collect f)))

;;; ------------------------------------------------------------ against Racket

(defun run-cases ()
  "Each (test label form) of cases.sexp must give what the Racket original
gave, as recorded in expected.sexp."
  (let ((expected (make-hash-table :test 'equal)))
    (dolist (e (read-all (test-file "expected.sexp")))
      (setf (gethash (first e) expected) (second e)))
    (dolist (c (read-all (test-file "cases.sexp")))
      (ecase (first c)
        (define
         (destructuring-bind ((name &rest args) &rest body) (rest c)
           (eval `(defun ,name ,args ,@body))))
        (test
         (destructuring-bind (label form) (rest c)
           (multiple-value-bind (want found) (gethash label expected)
             (if found
                 (report label
                         (handler-case (eval form)
                           (error (e) (list :error (princ-to-string e))))
                         want)
                 (progn (incf *failures*)
                        (format t "~&FAIL ~A: no expected answer; rerun gen-expected.rkt~%"
                                label))))))))))

;;; ------------------------------------------------------------ Lisp only

(defun run-matche ()
  (check "matche head/tail"
         (run* (q) (matche '(1 2 3) (`(,a . ,d) (== q (list a d)))))
         '((1 (2 3))))
  (check "matche clauses"
         (run* (q) (matche '(1 2 3)
                     (`(,x . ,r) (== q 1))
                     (`(,x ,y . ,r) (== q 2))
                     (`(,x) (== q 3))))
         '(1 2))
  (check "matche literal and whole"
         (run* (q) (fresh (v)
                     (matche v
                       ((a b) (== q 'literal))
                       (`,w (== w 5) (== q w)))
                     (== v '(a b))))
         '(literal))
  (check "matche repeated variable"
         (list (run* (q) (matche '(1 1) (`(,x ,x) (== q x))))
               (run* (q) (matche '(1 2) (`(,x ,x) (== q x)))))
         '((1) ()))
  (check "matche generates"
         (run* (q) (matche q (`(a ,x) (== x 1)) (`(b ,x ,y) (== x y))))
         '((a 1) (b |_.0| |_.0|)))
  (check "matche evaluates its subject once"
         (let ((n 0))
           (run* (q) (matche (progn (incf n) '(1)) (`(,x) (== q x))))
           n)
         1)
  (check "lambdae"
         (let ((swapo (lambdae (l out) (`((,a ,b) (,b ,a))))))
           (run* (q) (funcall swapo '(1 2) q)))
         '((2 1))))

(defun run-matchee ()
  ;; the first three are matchee-test.scm of Racket-miniKanren (recursive
  ;; branch), with the answers it gives under Racket
  (check "matchee: variables under ___ collect lists"
         (run* (q) (matchee '((1 (2 3)) (10 (2 30)) (100 (2 300)))
                     (`((,a (2 ,b)) ___) (== q `(,a ,b)))))
         '(((1 10 100) (3 30 300))))
  (check "matchee without ___ is matche"
         (run1 (q) (matchee '(1 2 3) (`(,x . ,r) (== q `(,x ,r)))))
         '((1 (2 3))))
  (check "matchee: every split"
         (run* (q) (matchee '(1 2 3) (`(,x ___ . ,r) (== q `(,x ,r)))))
         '((() (1 2 3)) ((1) (2 3)) ((1 2) (3)) ((1 2 3) ())))
  (check "matchee: nested ___ repeats per element"
         (run* (q) (matchee '((a 1 2) (b 3) (c))
                     (`((,k ,v ___) ___) (== q `(,k ,v)))))
         '(((a b c) ((1 2) (3) ()))))
  (check "matchee: literals around ___"
         (list (run* (q) (matchee '(x 1 2 3 y) (`(x ,n ___ y) (== q n))))
               (run* (q) (matchee '(1 2 3) (`(,n ___ 4) (== q n)))))
         '(((1 2 3)) ()))
  (check "matchee: two ___ in one list"
         (run* (q) (matchee '(a b 1 2)
                     (`(,s ___ ,n ___)
                      (for-eacho #'symbolo s) (for-eacho #'numbero n)
                      (== q `(,s ,n)))))
         '(((a b) (1 2))))
  (check "matchee generates"
         (run 3 (q) (matchee q (`((,a ,b) ___))))
         '(() ((|_.0| |_.1|)) ((|_.0| |_.1|) (|_.2| |_.3|))))
  (check "matchee literal clause"
         (run* (q) (matchee '(5) ((5) (== q 'lit)) (`(,x ___) (== q x))))
         '(lit (5))))

(defun run-hygiene ()
  ;; the macros bind names of their own around the user's goals
  (check "variables named c and f"
         (run* (q) (fresh (c f) (conde ((== c 1) (== f 2) (== q (list c f))))))
         '((1 2)))
  (check "conda with a variable named a"
         (run* (q) (fresh (a f) (conda ((== a 1) (== f 2) (== q (list a f))))))
         '((1 2)))
  (check "condu with variables named c and f"
         (run* (q) (fresh (c f) (condu ((== c 1) (== f 2) (== q (list c f))))))
         '((1 2)))
  (check "project with a variable named s"
         (run* (q) (fresh (s) (== s 2) (project (s) (== q (* s 10)))))
         '(20)))

(defun run-walk ()
  (let* ((x (var 'x)) (y (var 'y)) (z (var 'z)))
    (check "walk an alist" (walk x `((,z . 5) (,x . ,y) (,y . ,z))) 5)
    (check "walk a variable cycle stops"
           (var? (walk x `((,z . ,x) (,x . ,y) (,y . ,z))))
           t)
    (check "walk* names the knot"
           (walk* x `((,x . (,y ,x))))
           `(==> ,x (,y ,x)))
    (check "s-ext keeps both views"
           (let ((s (s-ext (s-ext (s-empty) x 1) y x)))
             (list (walk y s) (length (s-alist s)) (rhs (s-ref s x))))
           '(1 2 1))
    (check "prefix-S"
           (let* ((s0 (s-ext (s-empty) x 1))
                  (s1 (s-ext (s-ext s0 y 2) z 3)))
             (mapcar #'rhs (prefix-S s1 s0)))
           '(3 2))
    (check "unify equi-recursive"
           (let ((s (unify y `(a ,y) (unify x `(a ,x) (s-empty)))))
             (not (null (unify x y s))))
           t)))

(defun run-recursive-vars ()
  (check "recursive-varo"
         (run* (q) (fresh (x) (== x `(1 ,x)) (recursive-varo x) (== q 'yes)))
         '(yes))
  (check "recursive-varo through a chain"
         (run* (q) (fresh (x y) (== x y) (== y `(1 ,x)) (recursive-varo x) (== q 'yes)))
         '(yes))
  (check "recursive-varo on a finite term"
         (run* (q) (fresh (x) (== x '(1 2)) (recursive-varo x)))
         '())
  (check "varo" (run* (q) (fresh (x) (varo x) (== q 'yes))) '(yes))
  (check "varo on a value" (run* (q) (varo 1)) '())
  (check "unified-varo"
         (list (run* (q) (fresh (x) (unified-varo x)))
               (run* (q) (fresh (x) (== x 1) (unified-varo x) (== q 'yes))))
         '(() (yes)))
  (check "non-unified-varo"
         (run* (q) (fresh (x) (non-unified-varo x) (== q 'yes)))
         '(yes)))

(defun run-misc ()
  (check "nevero beside an answer" (run 1 (q) (conde (nevero) ((== q 1)))) '(1))
  (check "alwayso" (run 3 (q) alwayso) '(|_.0| |_.0| |_.0|))
  (check "run1 .. run40" (list (run1 (q) (membero q '(a b))) (run40 (q) (== q 1))) '((a) (1)))
  (check "booleano" (run* (q) (booleano q)) '(nil t))
  (check "reify into a chosen package"
         (let ((*reify-package* (find-package :keyword)))
           (run* (q) (fresh (x) (== q (list x)))))
         '((:|_.0|)))
  (check "'_.0 reads as the reified symbol"
         (eq (first (run* (q) succeed)) '_.0)
         t)
  (check "symbolo: () and t are not symbols"
         (list (run* (q) (symbolo nil)) (run* (q) (symbolo t)) (run* (q) (symbolo :k) (== q 1)))
         '(() () (1)))
  (check "a long list"
         (length (first (run 1 (q) (appendo (make-list 5000 :initial-element 1) '(2) q))))
         5001)
  (check "a large substitution"
         (let ((vs (loop repeat 3000 collect (var 'v))))
           (run* (q)
             (builde 2999 (lambda (i) (== (nth i vs) (nth (1+ i) vs))))
             (== (car (last vs)) 'end)
             (== q (first vs))))
         '(end)))

(defun run-tests ()
  "Run every test; print the failures and return true when there are none."
  (let ((*failures* 0)
        (*checks* 0)
        (*package* (find-package '#:clrkanren-test)))
    (run-cases)
    (run-matche)
    (run-matchee)
    (run-hygiene)
    (run-walk)
    (run-recursive-vars)
    (run-misc)
    (format t "~&~D checks, ~D failures~%" *checks* *failures*)
    (zerop *failures*)))
