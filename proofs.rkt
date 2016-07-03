#lang racket
(require "infrastructure.rkt")
(require zippers)

(require (for-syntax syntax/parse))

(provide (struct-out dependent-subgoal)
         (struct-out irrelevant-subgoal)
         (struct-out subgoal)
         (struct-out complete-proof)
         (struct-out refined-step)
         ;; Zipper stuff
         down/proof
         left/proof
         right/proof
         ;; General accessors
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

;;; A zipper frame pointing at a particular child of a refined node
(struct refined-step-frame
  (name goal rule left-children right-children extractor)
  #:transparent
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match-define (refined-step-frame name goal rule l r ext)
      frame)
    (refined-step name goal rule (append (reverse l) (list focus) r) ext)))

;;; A zipper frame pointing at a particular child of a complete proof
(struct complete-proof-frame
  (goal rule extract left-children right-children)
  #:transparent
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match-define (complete-proof-frame goal rule extract l r)
      frame)
    (complete-proof goal rule extract (append (reverse l) (list focus) r))))

(define (down/proof [which 0])
  (zipper-movement
   (lambda (z)
     (match z
       [(zipper (refined-step
                 name goal rule
                 (? (lambda (cs) (> (length cs) which)) children)
                 ext)
                context)
        (define-values (l r) (split-at children which))
        (define c (car r))
        (zipper c (cons (refined-step-frame
                         name goal rule
                         (reverse l) (cdr r) ext)
                        context))]
       [(zipper (complete-proof
                 goal rule extract
                 (? (lambda (cs) (> (length cs) which)) children))
                context)
        (define-values (l r) (split-at children which))
        (define c (car r))
        (zipper c (cons (complete-proof-frame
                         goal rule extract
                         (reverse l) (cdr r))
                        context))]
       [(zipper focus _)
        (raise-argument-error 'down/proof
                              (symbol->string "proof with children")
                              focus)]))
   (lambda (z)
     (match (zipper-focus z)
       [(refined-step _ _ _ children _) (> (length children) which)]
       [(complete-proof _ _ _ children) (> (length children) which)]
       [_ #f]))))

(define left/proof
  (zipper-movement
   (lambda (z)
     (match z
       [(zipper x (cons (refined-step-frame
                         name goal rule (cons l ls) rs ext)
                        context))
        (zipper l (cons (refined-step-frame
                         name goal rule ls (cons x rs) ext)
                        context))]
       [(zipper x (cons (refined-step-frame
                         name goal rule (list) rs ext)
                        context))
        (raise-argument-error 'left/proof
                              (symbol->string 'pair?)
                              '())]
       [(zipper x (cons (complete-proof-frame
                         goal rule extract (cons l ls) rs)
                        context))
        (zipper l (cons (complete-proof-frame
                         goal rule extract ls (cons x rs))
                        context))]
       [(zipper x (cons (complete-proof-frame
                         goal rule extract (list) rs)
                        context))
        (raise-argument-error 'left/proof
                              (symbol->string 'pair?)
                              '())]))
   (lambda (z)
     (match (zipper-context z)
       [(cons (or (refined-step-frame _ _ _ (cons _ _) _ _)
                  (complete-proof-frame _ _ _ (cons _ _) _)) _)
        #t]
       [_ #f]))))

(define right/proof
  (zipper-movement
   (lambda (z)
     (match z
       [(zipper x (cons (refined-step-frame
                         name goal rule ls (cons r rs) ext)
                        context))
        (zipper r (cons (refined-step-frame
                         name goal rule (cons x ls) rs ext)
                        context))]
       [(zipper x (cons (refined-step-frame
                         name goal rule ls (list) ext)
                        context))
        (raise-argument-error 'right/proof
                              (symbol->string 'pair?)
                              '())]
       [(zipper x (cons (complete-proof-frame
                         goal rule extract ls (cons r rs))
                        context))
        (zipper r (cons (complete-proof-frame
                         goal rule extract (cons x ls) rs)
                        context))]
       [(zipper x (cons (complete-proof-frame
                         goal rule extract ls (list))
                        context))
        (raise-argument-error 'right/proof
                              (symbol->string 'pair?)
                              '())]))
   (lambda (z)
     (match (zipper-context z)
       [(cons (or (refined-step-frame _ _ _ _ (cons _ _) _)
                  (complete-proof-frame _ _ _ _ (cons _ _))) _)
        #t]
       [_ #f]))))


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

