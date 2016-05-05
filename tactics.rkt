#lang racket

(require zippers)

(require "infrastructure.rkt" "error-handling.rkt" "proofs.rkt" "proof-state.rkt" "monad-notation.rkt")

(provide begin-for-subgoals first-success proof <- pure
         skip with-subgoals tactic-trace? trace try
         prove)

(module+ test
  (require rackunit))

;;; Executing tactics
(define tactic-trace? (make-parameter #f))

(define (pretty-hypothetical seq)
  `(>> ,(map (lambda (x)
               (cons (syntax->datum (car x)) (syntax->datum (cdr x))))
             (hypothetical-hypotheses seq))
       ,(syntax->datum (hypothetical-goal seq))))

(define/proof skip
  (pure (void)))

(define (try tactic)
  (first-success tactic
                 skip))

(define (first-success . tacs)
  (if (pair? tacs)
      (handle-errors (car tacs)
        [_ (apply first-success (cdr tacs))])
      (proof-fail "Alternatives exhausted.")))


(define (trace message)
  (displayln message)
  skip)

(define (list-split lst lengths)
  (if (null? lengths)
      (if (null? lst)
          empty
          (error 'length-mismatch))
      (let-values ([(start rest) (split-at lst (car lengths))])
        (cons start (list-split rest (cdr lengths))))))

;; Like Coq's ; tactical: first, run outer on the goal. If success,
;; run (begin-for-subgoals inner) on each subgoal.
(define (begin-for-subgoals outer . inner)
  (cond [(null? inner)
         outer]
        [else
         (proof outer
                (<- focus get-focus)
                (if (refined-step? focus)
                    (proof
                     (move down/refined-step-children)
                     (proof-while
                      (proof (<- f get-focus)
                             (pure (pair? f)))
                      (proof (move down/car)
                             (apply begin-for-subgoals inner)
                             (move up down/cdr))))
                    (proof-fail "didn't get a refined step")))]))

;;; When the focus is on an element of a list of subgoals, refine each
;;; of the remaining subgoals with the corresponding element of
;;; tacs. If they are different lengths, fail. On success, end with
;;; the focus on the parent node.
(define (in-subgoals . tacs)
  (proof
   (<- f get-focus)
   (if (and (list? f)
            (= (length f) (length tacs)))
       (proof (move down/list-first)
              (for/proof
               ([tac tacs])
               tac
               (<- can? (movement-possible? right/list))
               (if can?
                   (move right/list)
                   skip))
              (move up up))
       (proof-fail (make-exn:fail "Mismatched tactic script length"
                                  (current-continuation-marks))))))

;;; Run outer. Each of its subgoals must have a corresponding tactic
;;; in inner that does not fail, or else the whole thing fails.
(define (with-subgoals outer . inner)
  (proof outer
         (<- focus get-focus)
         (if (refined-step? focus)
             (proof
              (move down/refined-step-children)
              (apply in-subgoals inner))
             (proof-fail "didn't get a refined step"))))

