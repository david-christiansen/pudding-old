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
          refined-step))

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
  complete-proof
  refined-step)


