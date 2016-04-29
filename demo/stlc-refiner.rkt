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


;; Incredibly terrible proof search! Be careful with high search depths.
#;
(define-for-syntax (squish depth)
  (if (<= depth 0)
      (fail "Search depth exhausted")
      (apply first-success
             (append
              (for/list ([h (range 0 5)]) (assumption h))
              (list ;; addition is not here because it won't help me inhabit more types
               (int-intro 42)
               (string-intro "hej")
               (with-subgoals length-of-string (squish (- depth 1)))
               (with-subgoals (function-intro 'x) (squish (- depth 1)))
               (with-subgoals (application #'Int)
                 (squish (- depth 1))
                 (squish (- depth 1)))
               (with-subgoals (application #'String)
                 (squish (- depth 1))
                 (squish (- depth 1))))))))

;; A linear tactic script, dispatching subgoals as they arise
(define/refiner add-two (--> Int Int)
    (refine (function-intro 'n))
    (move down/refined-step-children)
    (move down/car)
    ;; Make sure that "try" works
    (try (refine (function-intro 'fnord)))
    (refine (addition 3))
    (move down/refined-step-children down/car)
    (refine (int-intro 1))
    solve
    (move up down/cdr down/car)
    (refine (assumption 0))
    solve
    (move up down/cdr down/car)
    (refine (int-intro 1))
    solve
    (move up up up up)
    solve
    (move up up)
    solve)

(define-for-syntax (by tac)
  (proof tac solve))

;; A tree-shaped tactic script, corresponding more closely to the goal
;; structure
(define/refiner add-2 (--> Int Int)
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

(define/refiner strlen (--> String Int)
  (proof
    (refine (function-intro 'str))
    (move down/refined-step-children down/car)
    (refine  length-of-string)
    (move down/refined-step-children down/car)
    (refine (assumption 0))
    solve
    (move up up)
    solve
    (move up up)
    solve))

(module+ test
  (check-equal? (add-two 4)
                6)

  (check-equal? (add-2 17)
                19)

  (check-equal? (strlen "halløjsa!") 9))
