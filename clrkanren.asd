;;;; clrkanren.asd

(defsystem "clrkanren"
  :description "Recursive miniKanren for Common Lisp: miniKanren whose unification takes self-referential bindings and names them (==> x t)."
  :author "Hirotaka Niitsuma"
  :license "MIT"
  :version "0.1.0"
  :pathname "src/"
  :serial t
  :components ((:file "package")
               (:file "mk")
               (:file "relations")
               (:file "matche"))
  :in-order-to ((test-op (test-op "clrkanren/test"))))

(defsystem "clrkanren/test"
  :description "Tests for clrkanren."
  :depends-on ("clrkanren")
  :pathname "test/"
  :serial t
  :components ((:file "tests"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call '#:clrkanren-test '#:run-tests)
               (error "clrkanren tests failed"))))
