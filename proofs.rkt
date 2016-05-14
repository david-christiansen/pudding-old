#lang racket
(require "infrastructure.rkt")
(require zippers)

(require (for-syntax syntax/parse))

(provide (struct-out dependent-subgoal)
         (struct-out irrelevant-subgoal)
         (struct-out subgoal)
         (struct-out complete-proof)
         (struct-out refined-step)
         (struct-zipper-out
          dependent-subgoal
          irrelevant-subgoal
          subgoal
          complete-proof
          refined-step)
         down/proof-step-children
         proof-step-goal
         proof-step?
         proof-step-children)

(module+ test
  (require rackunit))

;;; A subgoal that is waiting on something else. The waiting-for field
;;; contains a metavariable. When that metavariable is instantiated,
;;; the goal can be accessed by applying the procedure in next to the
;;; instantiation.
(struct dependent-subgoal (waiting-for next) #:transparent)

;;; An irrelevant subgoal. Hidden hypotheses will be made visible
;;; here, but it will not contribute an extract.
(struct irrelevant-subgoal (goal) #:transparent)

;;; An ordinary subgoal that's ready to be attacked. The name, which
;;; must be a metavariable, can appear at the head of dependent
;;; subgoals.
(struct subgoal (name goal) #:transparent)


;;; Complete proofs are those in which a rule has been applied and all
;;; subgoals have become complete-proofs.
(struct complete-proof (goal rule extract children) #:transparent)


;;; Refined nodes are not yet complete, but progress has been
;;; made. The children can be either subgoals, refined steps, or
;;; complete proofs.
(struct refined-step (name goal rule children extractor) #:transparent)


(define-struct-zipper-frames
  dependent-subgoal
  irrelevant-subgoal
  subgoal
  complete-proof refined-step)

(define (proof-step-goal prf)
  (match prf
    [(subgoal _ g) g]
    [(complete-proof g _ _ _) g]
    [(refined-step _ g _ _ _) g]
    [(irrelevant-subgoal g) g]
    [(dependent-subgoal mv f)
     (proof-step-goal (f mv))]))

(define (proof-step? x)
  (or (subgoal? x)
      (complete-proof? x)
      (refined-step? x)
      (irrelevant-subgoal? x)
      (dependent-subgoal? x)))

(define (proof-step-children prf)
  (match prf
    [(complete-proof _ _ _ cs) cs]
    [(refined-step _ _ _ cs _) cs]
    [_ #f]))

(define down/proof-step-children
  (zipper-movement
   (lambda (z)
     (cond [(complete-proof? (zipper-focus z))
            (down/complete-proof-children z)]
           [(refined-step? (zipper-focus z))
            (down/refined-step-children z)]))
   (lambda (z)
     (or (complete-proof? (zipper-focus z))
         (refined-step? (zipper-focus z))))))
