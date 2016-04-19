#lang racket

(require (for-syntax syntax/parse) "error-handling.rkt")

(provide (struct-out hypothesis)
         (struct-out hypothetical)
         unhide-all
         (struct-out refinement)
         (struct-out refinement-error)
         new-goal
         done-refining
         >>
         refinement-fail
         identity-refinement
         rule/c

         ;;; Subgoals
         relevant-subgoal
         irrelevant-subgoal
         named-subgoal
         subgoal?
         subgoal-obligation
         named-subgoal-name
         subgoal-relevant?)

(module+ test
  (require rackunit))

(struct hypothesis
  (name assumption relevant?)
  #:transparent)

;;; Contexts and such
;; hypotheses is an alist mapping identifiers to types, and goal is a type
(struct hypothetical
  (hypotheses goal)
  #:transparent)

(define-match-expander >>
  (syntax-parser
    [(>> h g) #'(hypothetical h g)])
  (syntax-parser
    [(>> h g) #'(hypothetical h g)]))

(define (unhide-all g)
  (match g
    [(>> hs goal)
     (>> (map (lambda (h)
                (hypothesis (hypothesis-name h)
                            (hypothesis-assumption h)
                            #t))
              hs)
         goal)]))

(define (new-goal goal)
  (>> empty goal))

(module+ test
  (check-equal? #t
                (match (new-goal #'15)
                  [(>> (list) (app syntax-e 15)) #t]
                  [_ #t])))

(struct irrelevant-subgoal (obligation) #:transparent)
(struct relevant-subgoal (obligation) #:transparent)
(struct named-subgoal (name obligation) #:transparent)

(define (subgoal? x)
  (or (irrelevant-subgoal? x)
      (relevant-subgoal? x)
      (named-subgoal? x)))

(define (subgoal-obligation subgoal)
  (match subgoal
    [(irrelevant-subgoal o) o]
    [(relevant-subgoal o) o]
    [(named-subgoal n o) o]))

(define (subgoal-relevant? g)
  (or (relevant-subgoal? g)
      (named-subgoal? g)))

;;; Refinement infrastructure
;;
;; 
;;
;; extraction should be a function from the new-goals' extracts to an extract
(struct refinement
  (new-goals extraction)
  #:transparent)

(define (done-refining term)
  (success (refinement empty (lambda _ term))))

(module+ test
  (check-equal? (syntax-e ((refinement-extraction
                            (success-value
                             (done-refining #'broccoli)))))
                'broccoli))

(struct refinement-error
  (rule-name goal message)
  #:transparent)

(define rule/c (-> hypothetical? (or/c failure? success?)))


(define (refinement-fail rule-name goal message)
  (failure (refinement-error rule-name goal message)))

(define/contract (identity-refinement goal)
  (-> subgoal? refinement?)
  (refinement (list goal)
              (lambda subterms
                (if (null? subterms)
                    (error "the impossible happened")
                    (car subterms)))))
