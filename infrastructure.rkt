#lang racket

(require (for-syntax syntax/parse))

(provide (struct-out sequent)
         (struct-out refinement)
         (struct-out exn:fail:refinement)
         new-goal
         done-refining
         rule/c
         >>
         raise-refinement-error
         identity-refinement)

(module+ test
  (require rackunit))

;;; Contexts and such
;; hypotheses is an alist mapping identifiers to types, and goal is a type
(struct sequent (hypotheses goal) #:transparent)

(define-match-expander >>
  (syntax-parser
    [(>> h g) #'(sequent h g)])
  (syntax-parser
    [(>> h g) #'(sequent h g)]))

(define (new-goal type) (>> empty type))

(module+ test
  (check-equal? #t
                (match (new-goal 15)
                  [(>> (list) 15) #t]
                  [_ #t])))

;;; Refinement infrastructure
;; extraction should be a function from a extracts to an extract
(struct refinement (new-goals extraction) #:transparent)


(define (done-refining term)
  (refinement empty (thunk* term)))

(module+ test
  (check-equal? ((refinement-extraction (done-refining 'broccoli)))
                'broccoli))

(define (identity-refinement goal)
  (refinement (list goal) identity))

(define rule/c (-> sequent? refinement?))

(struct exn:fail:refinement exn:fail (cant-refine) #:transparent)

(define (raise-refinement-error rule-name goal message)
  (raise (exn:fail:refinement
          (format "~a: cannot refine ~s~n~a" rule-name goal message)
          (current-continuation-marks)
          goal)))
