#lang racket

(require "stlc.rkt")
(require "text-ui.rkt")
(require "tactics.rkt")
(require (only-in "infrastructure.rkt" new-goal))

(define (stlc-prover goal)
  (prover goal (namespace-anchor->namespace stlc)))

(module+ test
  (define test-term
    (proof #'(--> String Int)
           (tactics (function-intro 'x)
                    length-of-string
                    (hypothesis 0))))
  (define add-two
    (proof #'(--> Int Int)
           (tactics (function-intro 'n)
                    (addition 3)
                    (int-intro 1)
                    (hypothesis 0)
                    (int-intro 1)))))


(module+ main
  (stlc-prover #'(--> String Int)))
