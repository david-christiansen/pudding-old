#lang racket

(require "../theories/stlc.rkt")
(require "../text-ui.rkt")
(require "../tactics.rkt")

(module stlc-prover-context racket/base
  (require "../theories/stlc.rkt")
  (require "../tactics.rkt")
  (require zippers)
  (require "../proof-state.rkt")
  (require "../proofs.rkt")

  (provide stlc-anchor)

  (define-namespace-anchor stlc-anchor))

(require
 'stlc-prover-context)

(define (stlc-prover goal)
  (prover goal (namespace-anchor->namespace stlc-anchor)))

(module+ main
  (stlc-prover #'(--> String Int)))


(module+ test
  (require rackunit)

  (define test-input
    (string-append
     "(refine (function-intro 'x))\n"
     "(move down/refined-step-children down/list-first)\n"
     "(refine length-of-string)\n"
     "(move down/refined-step-children down/list-first)\n"
     "(refine (assumption 0))\n"
     "solve\n"
     "(move up up)\n"
     "solve\n"
     "(move up up)\n"
     "solve\n"
     ":done"))


  (check-true
   (string?
    (with-output-to-string
      (thunk (with-input-from-string test-input
               (thunk (let ([res (stlc-prover #'(--> String Int))])
                        (displayln res)
                        (check-equal? (syntax->datum res)
                                      '(lambda (x) (string-length x)))))))))))
