#lang racket

(require "infrastructure.rkt" "error-handling.rkt")

(provide begin-for-subgoals begin-tactics fail first-success proof
         skip with-subgoals tactic-trace? trace try)

;;; Executing tactics
(define tactic-trace? (make-parameter #f))

(define (pretty-sequent seq)
  `(>> ,(map (lambda (x)
               (cons (syntax->datum (car x)) (syntax->datum (cdr x))))
             (sequent-hypotheses seq))
       ,(syntax->datum (sequent-goal seq))))

(define (goal-count r) (length (refinement-new-goals r)))

;; A zipper into an executing refinement tree
(struct tactics-frame
  (extracts
   subgoals
   extractor
   next))

;; A tactic script succeeds if it complete dispatches its subgoal
(define ((begin-tactics . tacs) goal)
  (let loop ([remaining-tactics tacs]
             [extracts empty]
             [subgoals (list goal)]
             [extractor (λ exts (if (cons? exts)
                                    (car exts)
                                    (error "The impossible happened!")))]
             [next #f])
    (when (tactic-trace?)
      (displayln "---- TACTIC STATE ----")
      (printf "\tRemaining tactics: ~a\n\tGoals:~a\n\n" remaining-tactics subgoals))

    (cond [(null? subgoals)
           (define this-extract
             (apply extractor (reverse extracts)))
           (when (tactic-trace?)
             (printf "\tExtract was ~a\n\n" this-extract))
           (match next
             [(tactics-frame old-extracts remaining-subgoals next-extractor next-next)
              (loop remaining-tactics
                    (cons this-extract old-extracts)
                    remaining-subgoals
                    next-extractor
                    next-next)]
             [#f (done-refining this-extract)])]

          [(null? remaining-tactics)
           (refinement-fail 'tactics
                            (car subgoals)
                            "No more tactics, but unsolved goals remain")]
          [else
           (error-do refinement-error
             (<- (refinement new-subgoals new-extractor)
                 ((car remaining-tactics) (car subgoals)))
             (loop (cdr remaining-tactics)
                   empty
                   new-subgoals
                   new-extractor
                   (tactics-frame extracts (cdr subgoals) extractor next)))])))

;; Attempt to prove goal completely using rule
(define (proof goal rule)
  (match (rule (new-goal goal))
    [(success (refinement (list) ext))
     (ext)]
    [(success other)
     (raise-result-error 'proof "complete proof" other)]
    [(failure (refinement-error rule-name bad-goal message))
     (raise-user-error "Error during proof" rule-name bad-goal message)]))

;;; A tactic, like a rule, is a function from a goal to a refinement.

(define ((first-success . rules) goal)
  (if (cons? rules)
      (match ((car rules) goal)
        [(? success? x) x]
        [(? failure? x) ((apply first-success (cdr rules)) goal)])
      (refinement-fail 'first-success goal "Alternatives exhausted.")))

(define (try tactic)
  (first-success tactic
                 skip))

;; A tactic that does nothing
(define (skip goal)
  (identity-refinement goal))

(define ((trace message) goal)
  (displayln message)
  (skip goal))

(define ((fail [message "Failed"]) goal)
  (refinement-fail 'fail goal message))

(define (list-split lst lengths)
  (if (null? lengths)
      (if (null? lst)
          empty
          (error 'length-mismatch))
      (let-values ([(start rest) (split-at lst (car lengths))])
        (cons start (list-split rest (cdr lengths))))))

;; Like Coq's ; tactical
(define ((begin-for-subgoals outer . inner) goal)
  (cond [(null? inner)
         (outer goal)]
        [else
         (error-do refinement-error
           [<- (refinement new-goals ext) (outer goal)]
           [<- subgoal-refinements
               (all-success
                (map (apply begin-for-subgoals inner) new-goals))]
           (let subgoal-counts (map goal-count subgoal-refinements))
           (success
            (refinement (append* (map refinement-new-goals subgoal-refinements))
                        (λ extraction-args
                          (define subgoal-extracts
                            (for/list ([r subgoal-refinements]
                                       [e (list-split extraction-args
                                                      subgoal-counts)])
                              (apply (refinement-extraction r) e)))
                          (apply ext subgoal-extracts)))))]))

;; Like JonPRL's ; with square brackets
(define ((with-subgoals outer . inner) goal)
  (error-do refinement-error
    (<- outer-res (outer goal))
    (match outer-res
     [(refinement new-goals extractor) #:when (= (length new-goals) (length inner))
      (error-do refinement-error
        (let potential-subgoal-refinements
             (for/list ([subgoal-tactic inner]
                        [this-subgoal new-goals])
               (subgoal-tactic this-subgoal)))
        (<- subgoal-refinements (all-success potential-subgoal-refinements))
        (let subgoal-counts (map goal-count
                                 subgoal-refinements))
        (pure
         (refinement (append* (map refinement-new-goals subgoal-refinements))
                     (λ extraction-args
                       (let ([subgoal-extracts
                              (map (λ (r e)
                                     (apply (refinement-extraction r) e))
                                   subgoal-refinements
                                   (list-split extraction-args subgoal-counts))])
                         (apply extractor subgoal-extracts))))))]
     [_ (refinement-fail 'subgoals goal "mismatched subgoal count")])))

