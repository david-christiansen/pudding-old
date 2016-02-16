#lang racket

(require (for-syntax syntax/parse) "error-handling.rkt")

(provide (struct-out sequent)
         (struct-out refinement)
         (struct-out refinement-error)
         new-goal
         done-refining
         >>
         refinement-fail
         identity-refinement
         rule/c)

(module+ test
  (require rackunit))

;;; Contexts and such
;; hypotheses is an alist mapping identifiers to types, and goal is a type
(struct sequent
  (hypotheses goal)
  #:transparent)

(define-match-expander >>
  (syntax-parser
    [(>> h g) #'(sequent h g)])
  (syntax-parser
    [(>> h g) #'(sequent h g)]))

(define (new-goal type) (>> empty type))

(module+ test
  (check-equal? #t
                (match (new-goal #'15)
                  [(>> (list) (app syntax-e 15)) #t]
                  [_ #t])))

;;; Refinement infrastructure
;; extraction should be a function from a extracts to an extract
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

(define rule/c (-> sequent? (or/c failure? success?)))


(define (refinement-fail rule-name goal message)
  (failure (refinement-error rule-name goal message)))

(define (identity-refinement goal)
  (success (refinement (list goal)
                       (lambda subterms
                         (if (null? subterms)
                             (error "the impossible happened")
                             (car subterms))))))
