#lang racket

(require
 ;; Make definitions with the refiner
 "refiner-define.rkt"
 ;; The theory and tactics we care about
 (for-syntax "stlc.rkt" "tactics.rkt" racket/list))

(module+ test
  (require rackunit))


;; Incredibly terrible proof search! Be careful with high search depths.
(define-for-syntax (squish depth)
  (if (<= depth 0)
      (fail "Search depth exhausted")
      (apply first-success
             (append
              (for/list ([h (range 0 5)]) (hypothesis h))
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
  (begin-tactics
    (function-intro 'n)
    ;; Make sure that "try" works
    (try (function-intro 'fnord))
    (addition 3)
    (int-intro 1)
    (hypothesis 0)
    (int-intro 1)))

;; A tree-shaped tactic script, corresponding more closely to the goal
;; structure
(define/refiner add-2 (--> Int Int)
  (with-subgoals (function-intro 'n)
    (with-subgoals (addition 3)
      (int-intro 1)
      (begin-tactics
        skip ;; start by doing nothing, just for the heck of it
        (hypothesis 0))
      (int-intro 1))))

(define/refiner another-test (--> Int (--> (--> Int String) String))
  (squish 3))

(module+ test
  (check-equal? (add-two 4) 6)
  (check-equal? (add-2 17) 19))
