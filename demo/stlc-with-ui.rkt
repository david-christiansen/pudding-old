#lang racket

(require "../theories/stlc.rkt")
(require "../text-ui.rkt")
(require "../tactics.rkt")

(define (stlc-prover goal)
  (prover goal (namespace-anchor->namespace stlc)))

(module+ test
  (define test-term
    (proof #'(--> String Int)
           (begin-tactics
             (function-intro 'x)
             length-of-string
             (hypothesis 0))))
  (define add-two
    (proof #'(--> Int Int)
           (begin-tactics
             (function-intro 'n)
             (addition 3)
             (int-intro 1)
             (hypothesis 0)
             (int-intro 1)))))


(module+ main
  (stlc-prover #'(--> String Int)))


(module+ test
  (require rackunit)

  (define test-input "(function-intro 'x)\nlength-of-string\n(hypothesis 0)\n")
  (check-equal?
   (with-input-from-string test-input
     (thunk* (with-output-to-string
               (thunk* (let ([res (stlc-prover #'(--> String Int))])
                         (check-equal? (syntax->datum res)
                                       '(lambda (x) (string-length x))))))))
   "At top.\n>> (--> String Int)\n> Position: 0 \n0. String\n>> Int\n> Position: 0 0 \n0. String\n>> String\n> "))
