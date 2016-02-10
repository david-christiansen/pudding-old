#lang racket

(require
 ;; Make definitions with the refiner
 "refiner-define.rkt"
 ;; The theory and tactics we care about
 (for-syntax "stlc.rkt" "tactics.rkt"))

(module+ test
  (require rackunit))

(define/refiner add-two (--> Int Int)
  (tactics (function-intro 'n)
           (addition 3)
           (int-intro 1)
           (hypothesis 0)
           (int-intro 1)))

(module+ test
  (check-equal? (add-two 4) 6))
