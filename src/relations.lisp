;;;; relations.lisp -- the usual miniKanren relations, the cyclic-list
;;;; relations of Niitsuma's Racket-miniKanren (recursive branch), and
;;;; Kiselyov's binary arithmetic.

(in-package #:clrkanren)

;;; ------------------------------------------------------------ lists

(defun caro (p a) (fresh (d) (== (cons a d) p)))
(defun cdro (p d) (fresh (a) (== (cons a d) p)))
(defun conso (a d p) (== (cons a d) p))
(defun nullo (x) (== '() x))
(defun eqo (x y) (== x y))
(defun pairo (p) (fresh (a d) (conso a d p)))

(defun booleano (x)
  (conde
    ((== nil x))
    ((== t x))))

(defun membero (x l)
  (conde
    ((fresh (a) (caro l a) (== a x)))
    ((fresh (d) (cdro l d) (membero x d)))))

(defun rembero (x l out)
  (conde
    ((nullo l) (== '() out))
    ((caro l x) (cdro l out))
    ((fresh (a d res)
       (conso a d l)
       (rembero x d res)
       (conso a res out)))))

(defun appendo (l s out)
  (conde
    ((nullo l) (== s out))
    ((fresh (a d res)
       (conso a d l)
       (conso a res out)
       (appendo d s res)))))

(defun flatteno (s out)
  (conde
    ((nullo s) (== '() out))
    ((pairo s)
     (fresh (a d res-a res-d)
       (conso a d s)
       (flatteno a res-a)
       (flatteno d res-d)
       (appendo res-a res-d out)))
    ((conso s '() out))))

(defun anyo (g)
  (conde
    (g)
    ((anyo g))))

(define-goal-constant nevero (anyo fail))
(define-goal-constant alwayso (anyo succeed))

;;; ------------------------------------------------------------ cyclic lists
;;;
;;; With recursive bindings, (appendo s r r) has answers: r is s repeated
;;; forever, and comes back as (==> x (s ... . x)).

(defun circular-listo (x o) (appendo x o o))

(defun truncated-circular-listo (x o)
  (fresh (y z)
    (pairo x)
    (circular-listo x z)
    (appendo o y z)))

;;; ------------------------------------------------------------ higher order

(defun mapo (fo ls q)
  (conde
    ((nullo ls) (== q '()))
    ((fresh (a d a^ d^)
       (conso a d ls)
       (conso a^ d^ q)
       (funcall fo a a^)
       (mapo fo d d^)))))

(defun for-eacho (fo ls)
  (conde
    ((nullo ls))
    ((fresh (a d)
       (conso a d ls)
       (funcall fo a)
       (for-eacho fo d)))))

(defun applye-nargs (f args n)
  (let ((vs (loop for i below n collect (var i))))
    (fresh ()
      (== vs args)
      (apply f vs))))

(defun for-eache (fo &rest lss)
  (let ((nargs (length lss)))
    (labels ((rec (lss)
               (conde
                 ((for-eacho #'nullo lss))
                 ((fresh (as ds)
                    (mapo #'caro lss as)
                    (mapo #'cdro lss ds)
                    (applye-nargs fo as nargs)
                    (rec ds))))))
      (rec lss))))

(defun builde (n f)
  "The conjunction of (F 0) ... (F N-1)."
  (labels ((rec (m)
             (if (>= m n)
                 succeed
                 (fresh ()
                   (funcall f m)
                   (rec (1+ m))))))
    (rec 0)))

(defun build2e (n m f)
  (builde n (lambda (i) (builde m (lambda (j) (funcall f i j))))))

(defun builde-nest (n-list f)
  (labels ((rec (n-lst i-lst)
             (if (null n-lst)
                 (apply f (reverse i-lst))
                 (builde (car n-lst)
                         (lambda (i) (rec (cdr n-lst) (cons i i-lst)))))))
    (rec n-list '())))

;;; ------------------------------------------------------------ variables

(defun varo (v)
  "V itself, unwalked, is a variable."
  (lambdag@ (c)
    (if (var? v) (unit c) (mzero))))

(defun unified-varo (v)
  "V has a binding."
  (lambdag@ (c B E S)
    (if (s-ref S v) (unit c) (mzero))))

(defun non-unified-varo (v)
  "V has no binding."
  (lambdag@ (c B E S)
    (if (s-ref S v) (mzero) (unit c))))

(defun recursive-var? (v S)
  "Whether V is bound, through a chain of variables, to a term that reaches
back to that chain: whether V stands for an infinite term."
  (and (var? v)
       (let ((chain '()) (u v))
         (loop for pr = (and (var? u) (not (memq u chain)) (s-ref S u))
               while pr
               do (push u chain)
                  (setf u (rhs pr)))
         (and chain
              (not (var? u))
              (let ((visited '()))
                (labels ((reach (tm)
                           (cond
                             ((var? tm)
                              (cond
                                ((memq tm chain) t)
                                ((memq tm visited) nil)
                                (t (push tm visited)
                                   (let ((pr (s-ref S tm)))
                                     (and pr (reach (rhs pr)))))))
                             ((consp tm) (or (reach (car tm)) (reach (cdr tm))))
                             (t nil))))
                  (reach u)))))))

(defun recursive-varo (v)
  (lambdag@ (c B E S)
    (if (recursive-var? v S) (unit c) (mzero))))

;;; ------------------------------------------------------------ arithmetic

(defun build-num (n)
  (cond
    ((oddp n) (cons 1 (build-num (floor (- n 1) 2))))
    ((and (not (zerop n)) (evenp n)) (cons 0 (build-num (floor n 2))))
    ((zerop n) '())))

(defun poso (n)
  (fresh (a d)
    (== `(,a . ,d) n)))

(defun >1o (n)
  (fresh (a ad dd)
    (== `(,a ,ad . ,dd) n)))

(defun full-addero (b x y r c)
  (conde
    ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
    ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
    ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
    ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
    ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
    ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
    ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
    ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))

(defun addero (d n m r)
  (conde
    ((== 0 d) (== '() m) (== n r))
    ((== 0 d) (== '() n) (== m r)
     (poso m))
    ((== 1 d) (== '() m)
     (addero 0 n '(1) r))
    ((== 1 d) (== '() n) (poso m)
     (addero 0 '(1) m r))
    ((== '(1) n) (== '(1) m)
     (fresh (a c)
       (== `(,a ,c) r)
       (full-addero d 1 1 a c)))
    ((== '(1) n) (gen-addero d n m r))
    ((== '(1) m) (>1o n) (>1o r)
     (addero d '(1) n r))
    ((>1o n) (gen-addero d n m r))))

(defun gen-addero (d n m r)
  (fresh (a b c e x y z)
    (== `(,a . ,x) n)
    (== `(,b . ,y) m) (poso y)
    (== `(,c . ,z) r) (poso z)
    (full-addero d a b c e)
    (addero e x y z)))

(defun pluso (n m k) (addero 0 n m k))

(defun minuso (n m k) (pluso m k n))

(defun *o (n m p)
  (conde
    ((== '() n) (== '() p))
    ((poso n) (== '() m) (== '() p))
    ((== '(1) n) (poso m) (== m p))
    ((>1o n) (== '(1) m) (== n p))
    ((fresh (x z)
       (== `(0 . ,x) n) (poso x)
       (== `(0 . ,z) p) (poso z)
       (>1o m)
       (*o x m z)))
    ((fresh (x y)
       (== `(1 . ,x) n) (poso x)
       (== `(0 . ,y) m) (poso y)
       (*o m n p)))
    ((fresh (x y)
       (== `(1 . ,x) n) (poso x)
       (== `(1 . ,y) m) (poso y)
       (odd-*o x n m p)))))

(defun odd-*o (x n m p)
  (fresh (q)
    (bound-*o q p n m)
    (*o x m q)
    (pluso `(0 . ,q) m p)))

(defun bound-*o (q p n m)
  (conde
    ((nullo q) (pairo p))
    ((fresh (x y z)
       (cdro q x)
       (cdro p y)
       (conde
         ((nullo n)
          (cdro m z)
          (bound-*o x y z '()))
         ((cdro n z)
          (bound-*o x y z m)))))))

(defun =lo (n m)
  (conde
    ((== '() n) (== '() m))
    ((== '(1) n) (== '(1) m))
    ((fresh (a x b y)
       (== `(,a . ,x) n) (poso x)
       (== `(,b . ,y) m) (poso y)
       (=lo x y)))))

(defun <lo (n m)
  (conde
    ((== '() n) (poso m))
    ((== '(1) n) (>1o m))
    ((fresh (a x b y)
       (== `(,a . ,x) n) (poso x)
       (== `(,b . ,y) m) (poso y)
       (<lo x y)))))

(defun <=lo (n m)
  (conde
    ((=lo n m))
    ((<lo n m))))

(defun <o (n m)
  (conde
    ((<lo n m))
    ((=lo n m)
     (fresh (x)
       (poso x)
       (pluso n x m)))))

(defun <=o (n m)
  (conde
    ((== n m))
    ((<o n m))))

(defun /o (n m q r)
  (conde
    ((== r n) (== '() q) (<o n m))
    ((== '(1) q) (=lo n m) (pluso r m n)
     (<o r m))
    ((<lo m n)
     (<o r m)
     (poso q)
     (fresh (nh nl qh ql qlm qlmr rr rh)
       (splito n r nl nh)
       (splito q r ql qh)
       (conde
         ((== '() nh)
          (== '() qh)
          (minuso nl r qlm)
          (*o ql m qlm))
         ((poso nh)
          (*o ql m qlm)
          (pluso qlm r qlmr)
          (minuso qlmr nl rr)
          (splito rr r '() rh)
          (/o nh m qh rh)))))))

(defun splito (n r l h)
  (conde
    ((== '() n) (== '() h) (== '() l))
    ((fresh (b n^)
       (== `(0 ,b . ,n^) n)
       (== '() r)
       (== `(,b . ,n^) h)
       (== '() l)))
    ((fresh (n^)
       (== `(1 . ,n^) n)
       (== '() r)
       (== n^ h)
       (== '(1) l)))
    ((fresh (b n^ a r^)
       (== `(0 ,b . ,n^) n)
       (== `(,a . ,r^) r)
       (== '() l)
       (splito `(,b . ,n^) r^ '() h)))
    ((fresh (n^ a r^)
       (== `(1 . ,n^) n)
       (== `(,a . ,r^) r)
       (== '(1) l)
       (splito n^ r^ '() h)))
    ((fresh (b n^ a r^ l^)
       (== `(,b . ,n^) n)
       (== `(,a . ,r^) r)
       (== `(,b . ,l^) l)
       (poso l^)
       (splito n^ r^ l^ h)))))

(defun logo (n b q r)
  (conde
    ((== '(1) n) (poso b) (== '() q) (== '() r))
    ((== '() q) (<o n b) (pluso r '(1) n))
    ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
    ((== '(1) b) (poso q) (pluso r '(1) n))
    ((== '() b) (poso q) (== r n))
    ((== '(0 1) b)
     (fresh (a ad dd)
       (poso dd)
       (== `(,a ,ad . ,dd) n)
       (exp2 n '() q)
       (fresh (s)
         (splito n dd r s))))
    ((fresh (a ad add ddd)
       (conde
         ((== '(1 1) b))
         ((== `(,a ,ad ,add . ,ddd) b))))
     (<lo b n)
     (fresh (bw1 bw nw nw1 ql1 ql s)
       (exp2 b '() bw1)
       (pluso bw1 '(1) bw)
       (<lo q n)
       (fresh (q1 bwq1)
         (pluso q '(1) q1)
         (*o bw q1 bwq1)
         (<o nw1 bwq1))
       (exp2 n '() nw1)
       (pluso nw1 '(1) nw)
       (/o nw bw ql1 s)
       (pluso ql '(1) ql1)
       (<=lo ql q)
       (fresh (bql qh s qdh qd)
         (repeated-mul b ql bql)
         (/o nw bw1 qh s)
         (pluso ql qdh qh)
         (pluso ql qd q)
         (<=o qd qdh)
         (fresh (bqd bq1 bq)
           (repeated-mul b qd bqd)
           (*o bql bqd bq)
           (*o b bq bq1)
           (pluso bq r n)
           (<o n bq1)))))))

(defun exp2 (n b q)
  (conde
    ((== '(1) n) (== '() q))
    ((>1o n) (== '(1) q)
     (fresh (s)
       (splito n b s '(1))))
    ((fresh (q1 b2)
       (== `(0 . ,q1) q)
       (poso q1)
       (<lo b n)
       (appendo b `(1 . ,b) b2)
       (exp2 n b2 q1)))
    ((fresh (q1 nh b2 s)
       (== `(1 . ,q1) q)
       (poso q1)
       (poso nh)
       (splito n b s nh)
       (appendo b `(1 . ,b) b2)
       (exp2 nh b2 q1)))))

(defun repeated-mul (n q nq)
  (conde
    ((poso n) (== '() q) (== '(1) nq))
    ((== '(1) q) (== n nq))
    ((>1o q)
     (fresh (q1 nq1)
       (pluso q1 '(1) q)
       (repeated-mul n q1 nq1)
       (*o nq1 n nq)))))

(defun expo (b q n)
  (logo n b q '()))
