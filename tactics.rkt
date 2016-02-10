#lang racket

(require "infrastructure.rkt")

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
(define ((begin-tactics . tacs) goal)
  (let loop ([remaining-tactics tacs]
             [extracts empty]
             [subgoals (list goal)]
             [extractor
              ;; The root "extractor" injects the extraction back into
              ;; the goal mechanism
              (λ (e) (refinement empty (thunk e)))]
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
           (raise-refinement-error 'tactics
                                   (car subgoals)
                                   "No more tactics, but unsolved goals remain")]
          [else
           (match ((car remaining-tactics) (car subgoals))
             [(refinement new-subgoals new-extractor)
              (loop (cdr remaining-tactics)
                    empty
                    new-subgoals
                    new-extractor
                    (tactics-frame extracts (cdr subgoals) extractor next))])])))

;; Attempt to prove goal completely using rule
(define (proof goal rule)
  (match (rule (new-goal goal))
    [(refinement (list) ext) (ext)]
    [_ (raise-refinement-error 'proof goal "proof did not completely solve goal.")]))

;;; A tactic, like a rule, is a function from a goal to a refinement.

(define ((first-success . rules) goal)
  (if (cons? rules)
      (with-handlers ([exn:fail:refinement?
                       (λ (e) ((apply first-success (cdr rules)) goal))])
        ((car rules) goal))
      (raise-refinement-error 'first-success goal "Alternatives exhausted.")))

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
  (raise-refinement-error 'fail goal message))

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
         (match-define (refinement new-goals ext) (outer goal))
         (define subgoal-refinements
           (map (apply begin-for-subgoals inner)
                new-goals))
         (define subgoal-counts
           (map (compose length refinement-new-goals)
                subgoal-refinements))

         (refinement (append* (map refinement-new-goals subgoal-refinements))
                     (λ extraction-args
                       (define subgoal-extracts
                         (for/list ([r subgoal-refinements]
                                    [e (list-split extraction-args
                                                   subgoal-counts)])
                           (apply (refinement-extraction r) e)))
                       (apply ext subgoal-extracts)))]))

;; Like JonPRL's ; with square brackets
(define ((with-subgoals outer . inner) goal)
  (match (outer goal)
    [(refinement new-goals extractor) #:when (= (length new-goals) (length inner))
     (let* ([subgoal-refinements (for/list ([subgoal-tactic inner]
                                            [this-subgoal new-goals])
                                   (subgoal-tactic this-subgoal))]
            [subgoal-counts (map (compose length refinement-new-goals)
                                 subgoal-refinements)])
       (refinement (append* (map refinement-new-goals subgoal-refinements))
                   (λ extraction-args
                     (let ([subgoal-extracts
                             (map (λ (r e)
                                    (apply (refinement-extraction r) e))
                                  subgoal-refinements
                                  (list-split extraction-args subgoal-counts))])
                        (apply extractor subgoal-extracts)))))]
    [_ (raise-refinement-error 'subgoals goal "mismatched subgoal count")]))
