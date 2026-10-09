#!/bin/sh
# Run the clrkanren test suite under SBCL.
cd "$(dirname "$0")" || exit 1
exec sbcl --noinform --non-interactive \
  --eval '(require :asdf)' \
  --eval '(push (truename ".") asdf:*central-registry*)' \
  --eval '(handler-case (progn (asdf:test-system "clrkanren") (uiop:quit 0))
            (error (e) (format t "~&~A~%" e) (uiop:quit 1)))'
