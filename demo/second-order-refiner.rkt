#lang racket


(require
 ;; Make definitions with the refiner
 "../refiner-define.rkt"
 ;; The theory and tactics we care about
 (for-syntax "../theories/second-order.rkt"
             "../tactics.rkt"
             "../proofs.rkt"
             "../proof-state.rkt"
             zippers
             racket/list))

(module+ test
  (require rackunit))

(define-for-syntax (solve-with rule)
  (proof (refine rule)
         solve))


(define/refiner identity #`(has-type #,(add-type-scopes #'(∀ α (→ α α))))
  (refine Forall-intro)
  (move (down/proof))
  (refine (function-intro 'x))
  (move (down/proof))
  (solve-with (assumption 0))
  (move up)
  solve
  (move up)
  solve)
