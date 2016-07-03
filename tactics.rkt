#lang racket

(require zippers)

(require "infrastructure.rkt" "error-handling.rkt" "proofs.rkt" "proof-state.rkt" "monad-notation.rkt")

(provide first-success proof <- pure skip
         with-subgoals with-subgoals*
         tactic-trace? trace try prove)

(module+ test
  (require rackunit))

;;; Executing tactics
(define tactic-trace? (make-parameter #f))

(define (pretty-sequent seq)
  `(>> ,(map (lambda (x)
               (cons (syntax->datum (car x)) (syntax->datum (cdr x))))
             (sequent-hypotheses seq))
       ,(syntax->datum (sequent-goal seq))))

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

;;; When the focus is on an element of a list of subgoals, refine each
;;; of the subgoals to the right with the corresponding element of
;;; tacs. If they are different lengths, fail. On success, end with
;;; the focus on the parent node.
(define (in-subgoals tacs)
  (proof
   (<- not-done? (movement-possible? right/proof))
   (match tacs
     [(list)
      (proof-fail (make-exn:fail
                   "No tactics provided to in-subgoals"
                   (current-continuation-marks)))]
     [(list t)
      (if not-done?
          (proof-fail (make-exn:fail
                       "Ran out of tactics early"
                       (current-continuation-marks)))
          (proof t (move up)))]
     [(list-rest t ts)
      (proof t
             (if not-done?
                 (proof (move right/proof)
                        (in-subgoals ts))
                 (proof-fail (make-exn:fail
                              "Ran out of subgoals early"
                              (current-continuation-marks)))))])))

;;; Run outer. Each of its subgoals must have a corresponding tactic
;;; in inner that does not fail, or else the whole thing fails.
(define (with-subgoals outer . inner)
  (proof outer
         (<- focus get-focus)
         (if (refined-step? focus)
             (proof
              (move (down/proof))
              (in-subgoals inner))
             (proof-fail (make-exn:fail "didn't get a refined step" (current-continuation-marks))))))


(define (with-subgoals* outer . inner)
  (proof (apply with-subgoals outer inner)
         solve))
