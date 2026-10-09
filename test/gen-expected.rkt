#lang racket
;;;; gen-expected.rkt -- run test/cases.sexp under the Racket original and
;;;; write test/expected.sexp, the answers the Common Lisp port must give.
;;;;
;;;;   racket test/gen-expected.rkt SCM2CPP-DIR
;;;;
;;;; SCM2CPP-DIR is a checkout of scm2cpp; the original is its
;;;; vendor/mk-recursive/mk.scm, the list relations are its
;;;; vendor/miniKanren-common.scm and the arithmetic is the one in its
;;;; vendor/rkanren/miniKanren.scm.

(define scm2cpp
  (match (current-command-line-arguments)
    [(vector dir) dir]
    [_ (error 'gen-expected "usage: racket gen-expected.rkt SCM2CPP-DIR")]))

(define test-dir
  (let ([p (syntax-source #'here)])
    (if (path? p)
        (let-values ([(dir name _) (split-path p)]) dir)
        (current-directory))))

(define ns (make-base-namespace))

(define (eval-defines path skip-first-line?)
  (with-input-from-file path
    (lambda ()
      (when skip-first-line? (read-line))
      (let loop ()
        (define f (read))
        (unless (eof-object? f)
          (when (and (pair? f) (memq (car f) '(define define-syntax)))
            (eval f ns))
          (loop))))))

(parameterize ([current-namespace ns])
  (namespace-require `(file ,(path->string (build-path scm2cpp "vendor" "mk-recursive" "mk.scm")))))
(eval-defines (build-path scm2cpp "vendor" "miniKanren-common.scm") #f)
(eval-defines (build-path scm2cpp "vendor" "rkanren" "miniKanren.scm") #t)

;; what clrkanren adds beside the original, as in Niitsuma's
;; Racket-miniKanren (recursive branch)
(for ([f '((define onceo (lambda (g) (condu (g))))
           (define (circular-listo x o) (appendo x o o))
           (define (truncated-circular-listo x o)
             (fresh (y z) (pairo x) (circular-listo x z) (appendo o y z)))
           (define mapo
             (lambda (fo ls q)
               (conde
                 [(nullo ls) (== q '())]
                 [(fresh (a d a^ d^) (conso a d ls) (conso a^ d^ q) (fo a a^) (mapo fo d d^))])))
           (define for-eacho
             (lambda (fo ls)
               (conde
                 [(nullo ls)]
                 [(fresh (a d) (conso a d ls) (fo a) (for-eacho fo d))])))
           (define (applye-nargs f args n)
             (let ([vs (build-list n var)])
               (fresh () (== vs args) (apply f vs))))
           (define for-eache
             (lambda (fo . lss)
               (let ([nargs (length lss)])
                 (let loop ([lss lss])
                   (conde
                     [(for-eacho nullo lss)]
                     [(fresh (as ds)
                        (mapo caro lss as)
                        (mapo cdro lss ds)
                        (applye-nargs fo as nargs)
                        (loop ds))])))))
           (define (builde n f)
             (let loop ([m 0])
               (if (>= m n) succeed (fresh () (f m) (loop (add1 m)))))))])
  (eval f ns))

(define cases
  (with-input-from-file (build-path test-dir "cases.sexp")
    (lambda ()
      (let loop ([acc '()])
        (define f (read))
        (if (eof-object? f) (reverse acc) (loop (cons f acc)))))))

(with-output-to-file (build-path test-dir "expected.sexp") #:exists 'replace
  (lambda ()
    (printf ";;;; expected.sexp -- written by gen-expected.rkt from cases.sexp; do not edit.\n")
    (for ([c cases])
      (match c
        [`(define . ,_) (eval c ns)]
        [`(test ,label ,form)
         (write (list label (eval form ns)))
         (newline)]))))
