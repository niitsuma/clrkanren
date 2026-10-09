# clrkanren — recursive miniKanren for Common Lisp

miniKanren whose unification accepts a variable bound to a term that contains
it, and names the resulting infinite term `(==> x t)` instead of failing.

```lisp
(run* (q)
  (fresh (x)
    (== x `(3 ,x))
    (== q `(1 5 ,x 7))))
;; => ((1 5 (==> _.0 (3 _.0)) 7))
```

`(==> _.0 (3 _.0))` reads as "`_.0`, where `_.0` is `(3 _.0)`": the list
`(3 3 3 ...)`. Stock miniKanren and cKanren return `()` here, because the
occurs check refuses the binding.

This is a Common Lisp (SBCL) port of `vendor/mk-recursive/mk.scm` from
[scm2cpp](https://github.com/niitsuma/scm2cpp), which is William Byrd's
miniKanren (`==`, `=/=`, `symbolo`, `numbero`, `absento`, `eigen`) carrying the
change from Hirotaka Niitsuma's recursive miniKanren:

> Hirotaka Niitsuma, *Context-Free Grammars Including Left Recursion using
> Recursive miniKanren*, Computación y Sistemas 22(4), 2018.
> https://doi.org/10.13053/cys-22-4-3072

The cyclic-list relations and the `varo` family come from
[niitsuma/Racket-miniKanren](https://github.com/niitsuma/Racket-miniKanren/tree/recursive)
(the `recursive` branch).

## What changes compared with miniKanren

- **Bindings may be self-referential.** `ext-s` doesn't run the occurs check.
- **Unification is equi-recursive.** Two terms are equal when their infinite
  unrollings are. A `(==> x t)` annotation is treated as `t`, and a pair of
  nodes that is already being compared counts as equal. That's what stops the
  recursion. So `x = (a x)` and `y = (a (a y))` unify, but `x = (a x)` and
  `y = (b y)` don't.
- **`walk*` names the knot.** When `walk*` meets a variable that is already on
  its own path, it wraps that binding as `(==> x t)`. The reifier shows the
  annotation with the usual `_.N` names.
- **The substitution is an association list plus a persistent hash trie** of
  the same bindings. `walk` looks bindings up in the trie, and `prefix-S` reads
  the list. On scm2cpp's whole-program type inference, this change turned
  half an hour into seventy seconds.

## Install

```lisp
(require :asdf)
(push #p"/path/to/clrkanren/" asdf:*central-registry*)   ; or put it under ~/common-lisp/
(asdf:load-system "clrkanren")
(use-package :clrkanren)    ; nickname: rkanren
```

The library has no dependencies beyond ASDF. It's tested on SBCL 2.5.

## Examples

The answers below are written the way Racket prints them. SBCL prints
`_.0` as `|_.0|` and folds symbols to upper case (see below).

```lisp
(run* (q) (== q `(,q)))
;; => ((==> _.0 (_.0)))

;; every cyclic list: r is s repeated forever
(run 5 (q) (fresh (r s) (appendo s r r) (== q r)))
;; => (_.0
;;     (_.0 ==> _.1 (_.0 . _.1))
;;     (_.0 ==> _.1 (_.2 _.0 . _.1))
;;     (_.0 ==> _.1 (_.2 _.3 _.0 . _.1))
;;     (_.0 ==> _.1 (_.2 _.3 _.4 _.0 . _.1)))

;; find the periods of a sequence
(run 5 (q) (truncated-circular-listo q '(1 2 3 4 1 2 3 4 1 2 3)))
;; => ((1 2 3 4)
;;     (1 2 3 4 1 2 3 4)
;;     (1 2 3 4 1 2 3 4 1 2 3)
;;     (1 2 3 4 1 2 3 4 1 2 3 _.0)
;;     (1 2 3 4 1 2 3 4 1 2 3 _.0 _.1))

;; different unrollings of one infinite term unify
(run* (q) (fresh (x y)
            (== x `(a ,x)) (== y `(a (a ,y)))
            (== x y) (== q 'same)))
;; => (SAME)

;; constraints
(run* (q) (fresh (a b)
            (absento 'x q) (== q `(,a ,b)) (symbolo b) (=/= a 5)))
;; => (((_.0 _.1) (=/= ((_.0 5)) ((_.1 x))) (sym _.1) (absento (x _.0))))

;; pattern matching
(defun swapo (l out)
  (matche l
    (`(,a ,b) (== out `(,b ,a)))))
(run* (q) (swapo '(1 2) q))
;; => ((2 1))
```

## Coming from the Scheme version

The names and the answers are the same as in the Racket original. The
differences are the ones Common Lisp imposes:

| Scheme                                  | clrkanren                                       |
|-----------------------------------------|-------------------------------------------------|
| `(define (appendo l s out) ...)`        | `(defun appendo (l s out) ...)`                 |
| `(mapo caro ls q)`                      | `(mapo #'caro ls q)`: relations are functions   |
| `(fo a a^)` on a relation held in `fo`  | `(funcall fo a a^)`                             |
| `'()` and `#f`                          | both are `nil`; `#t` is `t`                     |
| ``(matche x ((,a . ,d) g ...))``        | ``(matche x (`(,a . ,d) g ...))``: the pattern carries its own backquote |
| `(lambdag@ (c : B E S D Y N T) ...)`    | `(lambdag@ (c B E S D Y N TT) ...)`: `T` can't be a variable |

Some other points:

- **Case folds.** Common Lisp reads symbols in upper case. `D` and `d` are
  the same variable, and `'x` in an answer prints as `X`.
- **Reified names.** `_.0` prints as `|_.0|` because CL treats it as a
  potential number, but `'_.0` reads as the same symbol. The names are
  interned in `*package*` at the time of `run`, or in `*reify-package*` if you
  set it.
- **`symbolo`.** `nil` and `t` aren't symbols for `symbolo`, matching `'()`
  and `#t` in Scheme.
- **`matche` and SBCL.** `matche` reads unquoted variables out of SBCL's
  backquote representation, so it needs SBCL. The rest of the library is
  portable Common Lisp.

## API

- **Core:** `run`, `run*`, `run1` … `run40`, `fresh`, `conde`, `conda`,
  `condu`, `onceo`, `project`, `eigen`, `==`, `=/=`, `symbolo`, `numbero`,
  `absento`, `succeed`, `fail`, `var`, `var?`, `walk`, `walk*`, `unify`,
  `reify`, `lambdag@`, `case-inf`, `bind`, `mplus`, and the rest of the
  original's internals.
- **Recursion:** `recursive-representation?`, `make-recursive-representation`,
  `recursive-var?`, `recursive-varo`, `varo`, `unified-varo`,
  `non-unified-varo`, `circular-listo`, `truncated-circular-listo`.
- **Relations:** `caro`, `cdro`, `conso`, `nullo`, `eqo`, `pairo`, `booleano`,
  `membero`, `rembero`, `appendo`, `flatteno`, `anyo`, `nevero`, `alwayso`,
  `mapo`, `for-eacho`, `for-eache`, `builde`, `build2e`, `builde-nest`.
- **Arithmetic** (Kiselyov's binary numerals): `build-num`, `pluso`,
  `minuso`, `*o`, `/o`, `<o`, `<=o`, `logo`, `expo`, …
- **Matching:** `matche`, `lambdae`.

## Tests

```sh
./run-tests.sh                 # or (asdf:test-system "clrkanren")
```

`test/cases.sexp` lists programs in the subset of syntax that Scheme and Common
Lisp share. `test/gen-expected.rkt` runs them under the Racket original and
writes `test/expected.sexp`, and the CL suite checks that this port gives the
same answers. After you add a case, regenerate the expected answers:

```sh
racket test/gen-expected.rkt /path/to/scm2cpp
```

## 日本語での概要

clrkanren は、自己参照する束縛（`x = (3 x)` など）を occurs check で拒否せず、
そのまま受け入れる miniKanren を Common Lisp（SBCL）に移植したものです。
無限項は `(==> x t)` という形で名前を付けて返します。
scm2cpp の `vendor/mk-recursive/mk.scm`（Byrd の miniKanren に Niitsuma の
recursive miniKanren の変更を入れたもの）を、定義ごとに一対一で移植しています。
答えは Racket 版と同じになることを、差分テストで確認しています。

## License

MIT. See `LICENSE`.
