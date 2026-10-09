;;;; package.lisp -- the CLRKANREN package.

(defpackage #:clrkanren
  (:use #:common-lisp)
  (:nicknames #:rkanren)
  (:export
   ;; variables and terms
   #:var #:var? #:eigen? #:lhs #:rhs
   #:==> #:recursive-representation? #:make-recursive-representation
   ;; substitution
   #:s-empty #:s-hashed? #:s-ref #:s-ext #:s-alist #:prefix-S
   #:walk #:walk* #:unify #:unify* #:occurs-check
   ;; streams and goals
   #:mzero #:unit #:choice #:empty-f #:empty-c
   #:case-inf #:lambdag@ #:lambdaf@ #:inc #:bind #:bind* #:mplus #:mplus*
   #:c->B #:c->E #:c->S #:c->D #:c->Y #:c->N #:c->T
   #:fresh #:eigen #:conde #:conda #:condu #:ifa #:ifu #:project #:onceo
   #:run #:run* #:take_
   #:run1 #:run2 #:run3 #:run4 #:run5 #:run6 #:run7 #:run8 #:run9 #:run10
   #:run11 #:run12 #:run13 #:run14 #:run15 #:run16 #:run17 #:run18 #:run19 #:run20
   #:run21 #:run22 #:run23 #:run24 #:run25 #:run26 #:run27 #:run28 #:run29 #:run30
   #:run31 #:run32 #:run33 #:run34 #:run35 #:run36 #:run37 #:run38 #:run39 #:run40
   ;; constraints
   #:== #:=/= #:symbolo #:numbero #:absento #:succeed #:fail
   ;; reification
   #:reify #:reify-S #:reify-name #:*reify-package*
   #:sym #:num
   ;; recursive-binding utilities
   #:varo #:unified-varo #:non-unified-varo #:recursive-var? #:recursive-varo
   ;; relations
   #:caro #:cdro #:conso #:nullo #:eqo #:pairo #:booleano
   #:membero #:rembero #:appendo #:flatteno #:anyo #:nevero #:alwayso
   #:circular-listo #:truncated-circular-listo
   #:mapo #:for-eacho #:for-eache #:applye-nargs #:builde #:build2e #:builde-nest
   ;; Oleg numerals
   #:build-num #:poso #:>1o #:full-addero #:addero #:gen-addero #:pluso #:minuso
   #:*o #:odd-*o #:bound-*o #:=lo #:<lo #:<=lo #:<o #:<=o #:/o #:splito
   #:logo #:exp2 #:repeated-mul #:expo
   ;; pattern matching
   #:matche #:lambdae #:matchee #:___))
