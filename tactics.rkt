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

(define (first-success . tacs)
  (if (pair? tacs)
      (handle-errors (car tacs)
        [_ (apply first-success (cdr tacs))])
      (proof-fail "Alternatives exhausted.")))

(define (try tactic)
  (first-success tactic
                 skip))

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

;;; When the focus is on a list of subgoals, refine each of them with
;;; the corresponding element of tacs. If they are different lengths,
;;; fail. On success, end with the focus on the parent node.
(define (in-subgoals . tacs)
  (proof
   (<- f get-focus)
   (cond [(pair? f)
          (if (pair? tacs)
              (proof (move down/car)
                     (car tacs)
                     (move up down/cdr)
                     (apply in-subgoals (cdr tacs)))
              (proof-fail (make-exn:fail "Mismatched tactic script length: too few tactics"
                                         (current-continuation-marks))))]
         [(null? f)
          (if (null? tacs)
              ;; Refocus on parent
              (proof-while (proof (<- f get-focus)
                                  (pure (or (null? f) (pair? f))))
                           (move up))
              (proof-fail (make-exn:fail "Mismatched tactic script length: too many tactics"
                                         (current-continuation-marks))))]
         [else (proof-fail (make-exn:fail (format "Can't apply ~a at focus ~a"
                                                  'in-subgoals
                                                  f)
                                          (current-continuation-marks)))])))

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

