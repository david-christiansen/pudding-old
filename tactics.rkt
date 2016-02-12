#lang racket

(require "infrastructure.rkt" "error-handling.rkt")

(provide begin-for-subgoals begin-tactics fail first-success proof
         skip with-subgoals tactic-trace? trace try)

;;; Executing tactics
(define tactic-trace? (make-parameter #f))

(define (pretty-sequent seq)
  `(>> ,(map (lambda (x) (cons (syntax->datum (car x)) (syntax->datum (cdr x))))
             (sequent-hypotheses seq))
       ,(syntax->datum (sequent-goal seq))))

;; A zipper into an executing refinement tree
(struct tactics-frame (extracts subgoals extractor next))

;; A tactic script succeeds if it complete dispatches its subgoal
(define/contract ((begin-tactics . tacs) goal)
  (->* () #:rest (listof rule/c) rule/c)
  (let loop ([remaining-tactics tacs]
             [extracts empty]
             [subgoals (list goal)]
             [extractor
              ;; The root "extractor" injects the extraction back into
              ;; the goal mechanism
              (λ (e) (success (refinement empty (thunk e))))]
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
             [#f this-extract])]

          [(null? remaining-tactics)
           (refinement-fail 'tactics
                            (car subgoals)
                            "No more tactics, but unsolved goals remain")]
          [else
           (match-let! ([(refinement new-subgoals new-extractor)
                         ((car remaining-tactics) (car subgoals))])
             (loop (cdr remaining-tactics)
                   empty
                   new-subgoals
                   new-extractor
                   (tactics-frame extracts (cdr subgoals) extractor next)))])))

;; Attempt to prove goal completely using rule
(define/contract (proof goal rule)
  (-> syntax? rule/c syntax?)
  (match (rule (new-goal goal))
    [(success (refinement (list) ext))
     (ext)]
    [(success other)
     (raise-result-error 'proof "complete proof" other)]
    [(failure (refinement-error rule-name bad-goal message))
     (raise-user-error "Error during proof" rule-name bad-goal message)]))

;;; A tactic, like a rule, is a function from a goal to a refinement.

(define/contract ((first-success . rules) goal)
  (->* () #:rest (listof rule/c) rule/c)
  (if (cons? rules)
      (match ((car rules) goal)
        [(? success? x) x]
        [(? failure? x) ((apply first-success (cdr rules)) goal)])
      (refinement-fail 'first-success goal "Alternatives exhausted.")))

(define/contract (try tactic)
  (-> rule/c rule/c)
  (first-success tactic
                 skip))

;; A tactic that does nothing
(define/contract (skip goal)
  rule/c
  (identity-refinement goal))

(define/contract ((trace message) goal)
  (-> string? rule/c)
  (displayln message)
  (skip goal))

(define/contract ((fail [message "Failed"]) goal)
  (->* () (string?) rule/c)
  (refinement-fail 'fail goal message))

(define (list-split lst lengths)
  (if (null? lengths)
      (if (null? lst)
          empty
          (error 'length-mismatch))
      (let-values ([(start rest) (split-at lst (car lengths))])
        (cons start (list-split rest (cdr lengths))))))

;; Like Coq's ; tactical
(define/contract ((begin-for-subgoals outer . inner) goal)
  (->* (rule/c) #:rest (listof rule/c) rule/c)
  (cond [(null? inner)
         (outer goal)]
        [else
         (match-let! ([(refinement new-goals ext) (outer goal)]
                      [subgoal-refinements
                       (all-success
                        (map (apply begin-for-subgoals inner)
                             new-goals))])
           (let ([subgoal-counts
                  (map (compose length refinement-new-goals)
                       subgoal-refinements)])
             (success
              (refinement (append* (map refinement-new-goals subgoal-refinements))
                          (λ extraction-args
                            (define subgoal-extracts
                              (for/list ([r subgoal-refinements]
                                         [e (list-split extraction-args
                                                        subgoal-counts)])
                                (apply (refinement-extraction r) e)))
                            (apply ext subgoal-extracts))))))]))

;; Like JonPRL's ; with square brackets
(define/contract ((with-subgoals outer . inner) goal)
  (->* (rule/c) #:rest (listof rule/c) rule/c)
  (match! (outer goal)
    [(refinement new-goals extractor) #:when (= (length new-goals) (length inner))
     (let! ([subgoal-refinements (all-success
                                  (for/list ([subgoal-tactic inner]
                                             [this-subgoal new-goals])
                                    (subgoal-tactic this-subgoal)))])
       (let* ([subgoal-counts (map (compose length refinement-new-goals)
                                   subgoal-refinements)])
         (success
          (refinement (append* (map refinement-new-goals subgoal-refinements))
                      (λ extraction-args
                        (let ([subgoal-extracts
                               (map (λ (r e)
                                      (apply (refinement-extraction r) e))
                                    subgoal-refinements
                                    (list-split extraction-args subgoal-counts))])
                          (apply extractor subgoal-extracts)))))))]
    [_ (refinement-fail 'subgoals goal "mismatched subgoal count")]))
