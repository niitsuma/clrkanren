;;;; cases.sexp -- programs whose answers must agree with the Racket
;;;; original, vendor/mk-recursive/mk.scm of scm2cpp.
;;;;
;;;; The file is read by both sides.  gen-expected.rkt runs each case under
;;;; Racket and writes expected.sexp; tests.lisp runs it under SBCL and
;;;; compares.  An entry is either
;;;;
;;;;     (define (name arg ...) body ...)     a relation both sides define
;;;;     (test "label" form)                  a program and its answer
;;;;
;;;; so the forms are written in the part of the language Scheme and Common
;;;; Lisp share: no #t or #f, no named let, and a relation passed as an
;;;; argument is wrapped in a lambda (Common Lisp keeps functions apart).

;;; ---------------------------------------------------------------- basics

(test "== number" (run* (q) (== q 3)))
(test "== list" (run* (q) (== q '(1))))
(test "== clash" (run* (q) (== q 1) (== q 2)))
(test "fresh alias" (run* (q) (fresh (x y) (== x y) (== q (list x y)))))
(test "fresh pair" (run* (q) (fresh (x y) (== q `(,x ,y)))))
(test "fresh shared" (run* (q) (fresh (x y) (== y q) (== q `(,x ,y z)))))
(test "conde" (run* (q) (conde ((== q 1)) ((== q 2)) ((== q 3)))))
(test "conde nested"
  (run* (q) (fresh (x y)
              (conde ((== x 'a)) ((== x 'b)))
              (conde ((== y 1)) ((== y 2)))
              (== q (list x y)))))
(test "membero" (run* (q) (membero q '(a b c d))))
(test "membero 2" (run 2 (q) (membero 'x q)))
(test "appendo all splits" (run* (q) (fresh (x y) (appendo x y '(1 2 3)) (== q (list x y)))))
(test "appendo backwards" (run* (q) (appendo q '(c d) '(a b c d))))
(test "run multi" (run* (x y) (== x 1) (conde ((== y 2)) ((== y 3)))))
(test "run 0" (run 0 (q) (== q 1)))
(test "conda first" (run* (q) (conda ((== q 1)) ((== q 2)))))
(test "conda second" (run* (q) (conda (fail) ((== q 2)))))
(test "conda commits" (run* (q) (conda ((conde ((== q 1)) ((== q 2)))) ((== q 3)))))
(test "condu" (run* (q) (condu ((conde ((== q 1)) ((== q 2)))) ((== q 3)))))
(test "onceo" (run* (q) (onceo (membero q '(a b c)))))
(test "project" (run* (q) (fresh (x) (== x 3) (project (x) (== q (+ x 1))))))
(test "succeed" (run* (q) succeed))
(test "fail" (run* (q) fail))
(test "flatteno" (run 3 (q) (flatteno '((a b) c) q)))
(test "rembero" (run* (q) (rembero 'b '(a b c b) q)))
(test "strings" (run* (q) (== q "abc")))
(test "conso" (run* (q) (fresh (a d) (conso a d '(1 2 3)) (== q (list a d)))))

;;; ---------------------------------------------------------------- recursion
;;; The point of the library: a variable may be bound to a term that
;;; contains it, and the answer names the recursion as (==> x t).

(test "self list" (run* (q) (== q `(,q))))
(test "self via fresh" (run* (q) (fresh (x y) (== y q) (== q `(,x ,y)))))
(test "readme 1" (run* (q) (fresh (x) (== x `(3 ,x)) (== q `(1 5 ,x 7)))))
(test "self dotted" (run* (q) (fresh (x) (== x `(,x . ,x)) (== q x))))
(test "mutual" (run* (q) (fresh (x y) (== x `(f ,y)) (== y `(g ,x)) (== q x))))
(test "multi-var recursive" (run* (x y) (== x 1) (== y `(,x ,y))))
(test "same infinite term"
  (run* (q) (fresh (x y) (== x `(a ,x)) (== y `(a ,y)) (== x y) (== q 'ok))))
(test "different unrollings unify"
  (run* (q) (fresh (x y) (== x `(a ,x)) (== y `(a (a ,y))) (== x y) (== q `(,x ,y)))))
(test "different infinite terms"
  (run* (q) (fresh (x y) (== x `(a ,x)) (== y `(b ,y)) (== x y))))
(test "recursive then ground" (run* (q) (fresh (x) (== x `(1 . ,x)) (== x '(1 1 . 2)))))
(test "unroll matches" (run* (q) (fresh (x) (== x `(1 . ,x)) (== x `(1 1 . ,q)))))
(test "cyclic appendo" (run 5 (q) (fresh (r s) (appendo s r r) (== q r))))
(test "period detection"
  (run 5 (q) (fresh (r s u) (appendo s r r) (appendo '(1 2 1 2 1 2 1 2) u r) (== q s))))
(test "period of symbols"
  (run 3 (q) (fresh (r s u)
               (appendo s r r)
               (appendo '(for (gensym) in "abcd" for (gensym) in "abcd" for (gensym) in "abcd") u r)
               (== q s))))
(test "period with boundary"
  (run 5 (q) (fresh (r s u)
               (appendo s r r) (pairo s)
               (appendo '(1 2 3 4 1 2 3 4 1 2 3) u r)
               (== q s))))
(test "truncated-circular-listo"
  (run 5 (q) (truncated-circular-listo q '(1 2 3 4 1 2 3 4 1 2 3))))
(test "recursive =/= fails" (run* (q) (fresh (x y) (== x `(a ,x)) (== y `(a ,y)) (=/= x y))))
(test "recursive =/= holds" (run* (q) (fresh (x y) (== x `(a ,x)) (== y `(b ,y)) (=/= x y) (== q 'ok))))
(test "membero in cycle" (run 3 (q) (fresh (x) (== x `(1 2 . ,x)) (membero q x))))

;;; ---------------------------------------------------------------- =/=
;;; From cKanren's neqtests.scm; the expected forms are this reifier's.

(define (distincto l)
  (conde
    ((== l '()))
    ((fresh (a) (== l `(,a))))
    ((fresh (a ad dd)
       (== l `(,a ,ad . ,dd))
       (=/= a ad)
       (distincto `(,a . ,dd))
       (distincto `(,ad . ,dd))))))

(define (rembero-t x ls out)
  (conde
    ((== '() ls) (== '() out))
    ((fresh (a d res)
       (== `(,a . ,d) ls)
       (rembero-t x d res)
       (conde
         ((== a x) (== out res))
         ((== `(,a . ,res) out)))))))

(define (rembero-new x ls out)
  (conde
    ((== '() ls) (== '() out))
    ((fresh (a d res)
       (== `(,a . ,d) ls)
       (rembero-new x d res)
       (conde
         ((== a x) (== out res))
         ((=/= a x) (== `(,a . ,res) out)))))))

(test "=/=--1" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== `(,x ,y) q))))
(test "=/=-0" (run* (q) (fresh (x y z) (=/= `(,x 2 ,z) `(1 ,z 3)) (=/= `(,x 6 ,z) `(4 ,z 6)) (=/= `(,x ,y ,z) `(7 ,z 9)) (== x z) (== q `(,x ,y ,z)))))
(test "=/=-1" (run* (q) (=/= 3 q) (== q 3)))
(test "=/=-2" (run* (q) (== q 3) (=/= 3 q)))
(test "=/=-3" (run* (q) (fresh (x y) (=/= x y) (== x y))))
(test "=/=-4" (run* (q) (fresh (x y) (== x y) (=/= x y))))
(test "=/=-5" (run* (q) (fresh (x y) (=/= x y) (== 3 x) (== 3 y))))
(test "=/=-6" (run* (q) (fresh (x y) (== 3 x) (=/= x y) (== 3 y))))
(test "=/=-7" (run* (q) (fresh (x y) (== 3 x) (== 3 y) (=/= x y))))
(test "=/=-8" (run* (q) (fresh (x y) (== 3 x) (== 3 y) (=/= y x))))
(test "=/=-9" (run* (q) (fresh (x y z) (== x y) (== y z) (=/= x 4) (== z (+ 2 2)))))
(test "=/=-10" (run* (q) (fresh (x y z) (== x y) (== y z) (== z (+ 2 2)) (=/= x 4))))
(test "=/=-11" (run* (q) (fresh (x y z) (=/= x 4) (== y z) (== x y) (== z (+ 2 2)))))
(test "=/=-12" (run* (q) (fresh (x y z) (=/= x y) (== x `(0 ,z 1)) (== y `(0 1 1)))))
(test "=/=-13" (run* (q) (fresh (x y z) (=/= x y) (== x `(0 ,z 1)) (== y `(0 1 1)) (== z 1) (== `(,x ,y) q))))
(test "=/=-14" (run* (q) (fresh (x y z) (=/= x y) (== x `(0 ,z 1)) (== y `(0 1 1)) (== z 0))))
(test "=/=-15" (run* (q) (fresh (x y z) (== z 0) (=/= x y) (== x `(0 ,z 1)) (== y `(0 1 1)))))
(test "=/=-16" (run* (q) (fresh (x y z) (== x `(0 ,z 1)) (== y `(0 1 1)) (=/= x y))))
(test "=/=-17" (run* (q) (fresh (x y z) (== z 1) (=/= x y) (== x `(0 ,z 1)) (== y `(0 1 1)))))
(test "=/=-18" (run* (q) (fresh (x y z) (== z 1) (== x `(0 ,z 1)) (== y `(0 1 1)) (=/= x y))))
(test "=/=-19" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== x 2))))
(test "=/=-20" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== y 1))))
(test "=/=-21" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== x 2) (== y 1))))
(test "=/=-22" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== `(,x ,y) q))))
(test "=/=-23" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== x 2) (== `(,x ,y) q))))
(test "=/=-24" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== x 2) (== y 9) (== `(,x ,y) q))))
(test "=/=-25" (run* (q) (fresh (x y) (=/= `(,x 1) `(2 ,y)) (== x 2) (== y 1) (== `(,x ,y) q))))
(test "=/=-26" (run* (q) (fresh (a x z) (=/= a `(,x 1)) (== a `(,z 1)) (== x z))))
(test "=/=-27" (run* (q) (fresh (a x z) (=/= a `(,x 1)) (== a `(,z 1)) (== x 5) (== `(,x ,z) q))))
(test "=/=-28" (run* (q) (=/= 3 4)))
(test "=/=-29" (run* (q) (=/= 3 3)))
(test "=/=-30" (run* (q) (fresh (a) (=/= a 3) (== 3 a))))
(test "=/=-31" (run* (q) (fresh (a) (== 3 a) (=/= a 3))))
(test "=/=-32" (run* (q) (fresh (a) (== 3 a) (=/= a 4))))
(test "=/=-33" (run* (q) (=/= 4 q) (=/= 3 q)))
(test "=/=-34" (run* (q) (=/= q 5) (=/= q 5)))
(test "=/=-37" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= x y))))
(test "=/=-38" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= y x))))
(test "=/=-39" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= x y) (=/= y x))))
(test "=/=-40" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= x y) (=/= x y))))
(test "=/=-41" (run* (q) (=/= q 5) (=/= 5 q)))
(test "=/=-42" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= `(,x ,y) `(5 6)) (=/= x 5))))
(test "=/=-43" (run* (q) (fresh (x y) (== `(,x ,y) q) (=/= x 5) (=/= `(,x ,y) `(5 6)))))
(test "=/=-44" (run* (q) (fresh (x y) (=/= x 5) (=/= `(,x ,y) `(5 6)) (== `(,x ,y) q))))
(test "=/=-45" (run* (q) (fresh (x y) (=/= 5 x) (=/= `(,x ,y) '(5 6)) (== `(,x ,y) q))))
(test "=/=-46" (run* (q) (fresh (x y) (=/= 5 x) (=/= `(,y ,x) `(6 5)) (== `(,x ,y) q))))
(test "=/=-47" (run* (x) (fresh (y z) (=/= x `(,y 2)) (== x `(,z 2)))))
(test "=/=-48" (run* (x) (fresh (y z) (=/= x `(,y 2)) (== x `((,z) 2)))))
(test "=/=-49" (run* (x) (fresh (y z) (=/= x `((,y) 2)) (== x `(,z 2)))))
(test "=/=-50" (run* (q) (distincto `(2 3 ,q))))
(test "=/=-51" (run* (q) (rembero-t 'a '(a b a c) q)))
(test "=/=-52" (run* (q) (rembero-t 'a '(a b c) '(a b c))))
(test "=/=-53" (run* (q) (rembero-new 'a '(a b a c) q)))
(test "=/=-54" (run* (q) (rembero-new 'a '(a b c) '(a b c))))
(test "=/= conde" (run* (q) (fresh (x) (conde ((== x 1) (== q 2)) ((=/= x 1) (== q 3))) (== x 3))))

;;; ---------------------------------------------------------------- types

(test "numbero 2" (run* (q) (fresh (x y) (numbero x) (numbero y) (== q `(,x ,y)))))
(test "numbero ground" (run* (q) (numbero 5) (== q 'yes)))
(test "numbero symbol" (run* (q) (numbero 'a)))
(test "symbolo" (run* (q) (symbolo q)))
(test "symbolo ground" (run* (q) (symbolo q) (== q 'a)))
(test "symbolo number" (run* (q) (symbolo q) (== q 5)))
(test "symbolo numbero" (run* (q) (symbolo q) (numbero q)))
(test "symbolo =/=" (run* (q) (symbolo q) (=/= q 'a)))
(test "numbero =/= symbol" (run* (q) (numbero q) (=/= q 'a)))
(test "symbolo pair" (run* (q) (fresh (a b) (symbolo a) (numbero b) (== q `(,a ,b)))))
(test "type mismatch =/=" (run* (q) (fresh (a b) (symbolo a) (numbero b) (=/= a b) (== q `(,a ,b)))))

;;; ---------------------------------------------------------------- absento

(test "absento" (run* (q) (absento 'x q)))
(test "absento fail" (run* (q) (absento 'x q) (== q '(a (x)))))
(test "absento ok" (run* (q) (absento 'x q) (== q '(a (b)))))
(test "absento mix" (run* (q) (fresh (a b) (absento 'x q) (== q `(,a ,b)) (symbolo b) (=/= a 5))))
(test "absento number" (run* (q) (fresh (a) (absento 3 a) (numbero a) (== q a))))
(test "absento symbol" (run* (q) (fresh (a) (absento 'c a) (symbolo a) (== q a))))
(test "absento split" (run* (q) (fresh (a b) (absento 'x `(,a . ,b)) (== q `(,a ,b)))))
(test "absento dup" (run* (q) (absento 'x q) (absento 'x q)))

;;; ---------------------------------------------------------------- eigen

(test "eigen" (run* (q) (eigen (e) (== q e))))
(test "eigen free" (run* (q) (eigen (e) (== q 1))))
(test "eigen inner" (run* (q) (eigen (e) (fresh (x) (== x e)))))

;;; ---------------------------------------------------------------- arithmetic

(test "build-num" (run* (q) (== q (build-num 13))))
(test "pluso" (run* (q) (pluso (build-num 3) (build-num 4) q)))
(test "pluso split" (run* (q) (fresh (x y) (pluso x y (build-num 3)) (== q `(,x ,y)))))
(test "minuso" (run* (q) (minuso (build-num 9) (build-num 4) q)))
(test "*o" (run* (q) (*o (build-num 6) (build-num 7) q)))
(test "*o factors" (run* (q) (fresh (x y) (*o x y (build-num 6)) (== q `(,x ,y)))))
(test "/o" (run* (q) (fresh (n r) (/o (build-num 17) (build-num 5) n r) (== q `(,n ,r)))))
(test "<o" (run* (q) (<o q (build-num 4))))
(test "<=o" (run* (q) (<=o q (build-num 2))))
(test "logo" (run* (q) (fresh (r) (logo (build-num 14) (build-num 2) q r))))
(test "expo" (run* (q) (expo (build-num 3) (build-num 2) q)))

;;; ---------------------------------------------------------------- higher order

(test "mapo" (run* (q) (mapo (lambda (p a) (caro p a)) '((1 2) (3 4)) q)))
(test "for-eacho" (run* (q) (for-eacho (lambda (p) (pairo p)) '((1) (2)))))
(test "for-eache" (run* (q) (for-eache (lambda (x y) (== x y)) '(2 3 4) q)))
(test "builde" (run 1 (q) (builde 3 (lambda (i) (membero i q)))))
