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

;;; ------------------------------------------------------------ fd

;;; fdtests.scm and comptests.scm of cKanren, with the answers they give
;;; there.  #t of tests 9 to 11 is t.

(defun add-digitso (augend addend carry-in carry digit)
  (fresh (partial-sum sum)
    (infd partial-sum (range 0 18))
    (infd sum (range 0 19))
    (plusfd augend addend partial-sum)
    (plusfd partial-sum carry-in sum)
    (conde
      ((<fd 9 sum) (=fd carry 1) (plusfd digit 10 sum))
      ((<=fd sum 9) (=fd carry 0) (=fd digit sum)))))

(defun send-more-moneyo (letters)
  (fresh (s e n d m o r y carry0 carry1 carry2)
    (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
    (distinctfd letters)
    (infd s m (range 1 9))
    (infd e n d o r y (range 0 9))
    (infd carry0 carry1 carry2 (range 0 1))
    (add-digitso s m carry2 m o)
    (add-digitso e o carry1 carry2 n)
    (add-digitso n r carry0 carry1 e)
    (add-digitso d e 0 carry0 y)))

(defun diago (qi qj d rng)
  (fresh (qi+d qj+d)
    (infd qi+d qj+d rng)
    (plusfd qi d qi+d)
    (=/=fd qi+d qj)
    (plusfd qj d qj+d)
    (=/=fd qj+d qi)))

(defun diagonalso (n l)
  (labels ((lp (r s i j)
             (cond
               ((or (null r) (null (cdr r))) succeed)
               ((null s) (lp (cdr r) (cddr r) (+ i 1) (+ i 2)))
               (t (fresh ()
                    (diago (car r) (car s) (- j i) (range 0 (* 2 n)))
                    (lp r (cdr s) i (+ j 1)))))))
    (lp l (cdr l) 0 1)))

(defun n-queenso (q* n)
  (labels ((lp (i l)
             (if (zerop i)
                 (fresh () (distinctfd l) (diagonalso n l) (== q* l))
                 (fresh (x)
                   (infd x (range 1 n))
                   (lp (- i 1) (cons x l))))))
    (lp n '())))

(defun max-val (n)
  (ecase n (1 9) (10 99) (100 999) (1000 9999) (10000 99999)))

(defun actual-wortho (ls out)
  (labels ((lp (ls place acc)
             (if (null ls)
                 (== acc out)
                 (fresh (cur acc^)
                   (infd acc^ (range 0 (max-val place)))
                   (infd cur (range 0 (- (* place 10) 1)))
                   (timesfd (car ls) place cur)
                   (plusfd acc cur acc^)
                   (lp (cdr ls) (* place 10) acc^)))))
    (lp (reverse ls) 1 0)))

(defun smm-mult (letters)
  (fresh (s e n d m o r y send more money)
    (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
    (distinctfd letters)
    (infd s m (range 1 9))
    (infd e n d o r y (range 0 9))
    (infd send more (range 0 9999))
    (infd money (range 0 99999))
    (actual-wortho `(,s ,e ,n ,d) send)
    (actual-wortho `(,m ,o ,r ,e) more)
    (actual-wortho `(,m ,o ,n ,e ,y) money)
    (plusfd send more money)))

(defun fd-distincto (l)
  (conde
    ((== l '()))
    ((fresh (a) (== l `(,a))))
    ((fresh (a ad dd)
       (== l `(,a ,ad . ,dd))
       (=/= a ad)
       (fd-distincto `(,a . ,dd))
       (fd-distincto `(,ad . ,dd))))))

(defun run-fd ()
  (check "fd 0.0" (run* (x) (infd x '(1 2))) '(1 2))
  (check "fd 0.1" (run* (x) (fresh (y) (infd x y '(1 2)) (=fd x y))) '(1 2))
  (check "fd 1.0" (run* (x) (infd x '(1 2)) (=/=fd x 1)) '(2))
  (check "fd 1.1"
         (run* (q) (fresh (x) (infd x q '(1 2)) (=/=fd x 1) (=fd x q)))
         '(2))
  (check "fd 2"
         (run* (q) (fresh (x y z)
                     (infd x '(1 2 3)) (infd y '(3 4 5)) (=fd x y)
                     (infd z '(1 3 5 7 8)) (infd z '(5 6)) (=fd z 5)
                     (== q `(,x ,y ,z))))
         '((3 3 5)))
  (check "fd 3"
         (run* (q) (fresh (x y z)
                     (infd x '(1 2 3)) (infd y '(3 4 5)) (=fd x y)
                     (infd z '(1 3 5 7 8)) (infd z '(5 6)) (=fd z x)
                     (== q `(,x ,y ,z))))
         '())
  (check "fd 4"
         (run* (q) (fresh (x y z)
                     (infd x '(1 2)) (infd y '(2 3)) (infd z q '(2 4))
                     (=fd x y) (=/=fd x z) (=fd q z)))
         '(4))
  (check "fd 4.1"
         (run* (q) (fresh (x y z)
                     (=fd x y) (infd y '(2 3)) (=/=fd x z)
                     (infd z q '(2 4)) (=fd q z) (infd x '(1 2))))
         '(4))
  (check "fd 5"
         (run* (q) (fresh (x y)
                     (infd x '(1 2 3)) (infd y '(0 1 2 3 4))
                     (<fd x y) (=/=fd x 1) (=fd y 3)
                     (== q `(,x ,y))))
         '((2 3)))
  (check "fd 6"
         (run* (q) (fresh (x y)
                     (infd x '(1 2)) (infd y '(2 3)) (=fd x y) (== q `(,x ,y))))
         '((2 2)))
  (check "fd 7"
         (run* (q)
           (fresh (x y z) (infd x y z '(1 2)) (=/=fd x y) (=/=fd x z) (=/=fd y z))
           (infd q '(5)))
         '())
  (check "fd 8" (run* (q) (fresh (x) (infd x '(1 2))) (infd q '(5))) '(5))
  (check "fd 9" (run* (q) (== q t)) '(t))
  (check "fd 10" (run* (q) (infd q '(1 2)) (== q t)) '())
  (check "fd 11" (run* (q) (== q t) (infd q '(1 2))) '())
  (check "fd 12"
         (run* (q) (fresh (x) (<=fd x 5) (infd x q (range 0 10)) (=fd q x)))
         '(0 1 2 3 4 5))
  (check "fd 13"
         (run* (q) (fresh (x y z)
                     (infd x y z q (range 0 9))
                     (=/=fd x y) (=/=fd y z) (=/=fd x z)
                     (=fd x 2) (=fd q 3) (plusfd y 3 z)))
         '(3))
  (check "fd 14.0" (run* (q) (distinctfd '(1 2 3 4 5))) '(|_.0|))
  (check "fd 14.1" (run* (q) (distinctfd '(1 2 3 4 4 5))) '())
  (check "fd 14.2" (run* (q) (infd q (range 0 2)) (distinctfd `(,q))) '(0 1 2))
  (check "fd 14.3" (run* (q) (infd q (range 0 2)) (distinctfd `(,q ,q))) '())
  (check "fd 14.4"
         (run* (q) (fresh (x y z)
                     (infd x y z (range 0 2))
                     (distinctfd `(,x ,y ,z))
                     (== q `(,x ,y ,z))))
         '((0 1 2) (0 2 1) (1 0 2) (2 0 1) (1 2 0) (2 1 0)))
  (check "fd 15"
         (run* (q) (fresh (a b c x)
                     (infd a b c (range 1 3))
                     (distinctfd `(,a ,b ,c))
                     (=/=fd c x) (<=fd b 2) (== x 3)
                     (== q `(,a ,b ,c))))
         '((3 1 2) (3 2 1)))
  (check "fd 16"
         (run* (q) (fresh (x y z) (infd x y z '(1 2)) (distinctfd `(,x ,y ,z))))
         '())
  (check "fd 17"
         (run* (q) (fresh (x y) (infd x y (range 0 6)) (timesfd x y 6) (== q `(,x ,y))))
         '((1 6) (2 3) (3 2) (6 1)))
  (check "fd 18"
         (run* (q) (fresh (x y) (infd x y (range 0 6)) (timesfd x 6 y) (== q `(,x ,y))))
         '((0 0) (1 6)))
  (check "fd 19"
         (run* (q) (fresh (x y) (infd x y (range 0 6)) (timesfd 6 x y) (== q `(,x ,y))))
         '((0 0) (1 6)))
  (check "fd 20" (run* (q) (infd q (range 0 36)) (timesfd q q 36)) '(6))
  (check "fd 21"
         (run* (q) (fresh (x y) (infd x y (range 1 100)) (timesfd x y 0) (== q 5)))
         '())
  (check "fd long-addition-step"
         (run* (q) (fresh (digit1 digit2 carry0 carry1)
                     (infd carry0 carry1 (range 0 1))
                     (infd digit1 digit2 (range 0 9))
                     (add-digitso 4 9 0 carry0 digit1)
                     (add-digitso 3 8 carry0 carry1 digit2)
                     (== q `(,carry1 ,digit2 ,digit1))))
         '((1 2 3)))
  (check "fd 30" (run* (q) (actual-wortho '(1 2 3) 123)) '(|_.0|))
  (check "fd 31"
         (run* (q) (fresh (x y z)
                     (infd x y z (range 0 9))
                     (== q `(,x ,y ,z))
                     (actual-wortho `(,x ,y ,z) 123)))
         '((1 2 3)))
  (check "fd 32" (run* (q) (infd q (range 0 999)) (actual-wortho '(1 2 3) q)) '(123))
  (check "fd 33" (run* (q) (infd q (range 0 9)) (actual-wortho `(5 ,q 3) 543)) '(4))
  (check "fd 34"
         (run* (q) (fresh (x)
                     (infd x (range 0 9))
                     (infd q (range 0 999))
                     (actual-wortho `(5 ,x 3) q)))
         '(503 513 523 533 543 553 563 573 583 593))
  (check "send more money"
         (run* (q) (send-more-moneyo q))
         '((9 5 6 7 1 0 8 2)))
  (check "send more money (multiplication)"
         (run* (q) (smm-mult q))
         '((9 5 6 7 1 0 8 2)))
  (check "eight queens"
         (length (run* (q) (n-queenso q 8)))
         92)
  ;; comptests.scm: fd beside =/=
  (check "Distinct Queens 1"
         (run* (q) (fresh (x) (n-queenso x 8) (fd-distincto x)))
         '(|_.0|))
  (check "Distinct Queens 2"
         (let ((answers (run* (q) (n-queenso q 4))))
           (run* (q) (fd-distincto answers)))
         '(|_.0|))
  (check "infd/Distinct 1"
         (run* (q) (infd q '(2 3 4)) (fd-distincto `(a 3 ,q)))
         '(2 4))
  ;; here only
  (check "fd beside a recursive binding"
         (run* (q) (fresh (x n)
                     (infd n (range 1 3))
                     (== x `(,n ,x))
                     (=/=fd n 2)
                     (== q x)))
         '((1 (==> |_.0| (1 |_.0|))) (3 (==> |_.0| (3 |_.0|)))))
  (check "fd without a domain is an error"
         (handler-case (progn (run* (q) (fresh (x) (<=fd x q) (infd q '(1)))) :answered)
           (error () :error))
         :error))

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
    (run-fd)
    (run-hygiene)
    (run-walk)
    (run-recursive-vars)
    (run-misc)
    (format t "~&~D checks, ~D failures~%" *checks* *failures*)
    (zerop *failures*)))
