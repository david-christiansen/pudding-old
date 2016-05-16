#lang racket

(require
 ;; Make definitions with the refiner
 "../refiner-define.rkt"
 ;; The theory and tactics we care about
 (for-syntax "../theories/stlc.rkt" "../tactics.rkt" "../proofs.rkt"
             "../proof-state.rkt"
             zippers
             racket/list))

(module+ test
  (require rackunit))


;; A linear tactic script, dispatching subgoals as they arise
(define/refiner add-two #'(--> Int Int)
    (refine (function-intro 'n))
    (move down/refined-step-children)
    (move down/list-first)
    ;; Make sure that "try" works
    (try (refine (function-intro 'fnord)))
    (refine (addition 3))
    (move down/refined-step-children down/list-first)
    (refine (int-intro 1))
    solve
    (move right/list)
    (refine (assumption 0))
    solve
    (move right/list)
    (refine (int-intro 1))
    solve
    (move up up)
    solve
    (move up up)
    solve)

(define-for-syntax (by tac)
  (proof tac solve))

;; A tree-shaped tactic script, corresponding more closely to the goal
;; structure

(define/refiner add-2 #'(--> Int Int)
  (with-subgoals (refine (function-intro 'n))
    (by
     (with-subgoals (refine (addition 3))
       (by (refine (int-intro 1)))
       (proof
        skip ;; start by doing nothing, just for the heck of it
        (refine (assumption 0))
        solve)
       (proof (refine (int-intro 1))
              solve))))
  solve)

(define/refiner strlen #'(--> String Int)
  (proof
    (refine (function-intro 'str))
    (move down/refined-step-children down/list-first)
    (refine length-of-string)
    (move down/refined-step-children down/list-first)
    (refine (assumption 0))
    solve
    (move up up)
    solve
    (move up up)
    solve))

(define/refiner twice-string-length #'(--> String Int)
  (with-subgoals (refine (function-intro 'str))
    (by (with-subgoals (refine (addition 2))
          (proof (refine length-of-string)
                 (move down/proof-step-children down/list-first)
                 (by (refine (assumption 0)))
                 (move up up)
                 solve)
          (proof (refine length-of-string)
                 (move down/proof-step-children down/list-first)
                 (by (refine (assumption 0)))
                 (move up up)
                 solve))))
  solve)

(module+ test
  (check-equal? (add-two 4)
                6)

  (check-equal? (add-2 17)
                19)

  (check-equal? (strlen "halløjsa!") 9))
