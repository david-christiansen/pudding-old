#lang racket

(require (for-syntax syntax/parse) "error-handling.rkt" "metavariables.rkt")

(provide (struct-out hypothesis)
         (struct-out sequent)
         unhide-all
         (struct-out refinement)
         new-goal
         done-refining
         >>
         rule/c)

(module+ test
  (require rackunit))

(struct hypothesis
  (name assumption relevant?)
  #:transparent)

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

;;; Refinement infrastructure
;;
;; 
;;
;; extraction should be a function from the new-goals' extracts to an extract
(struct refinement
  (new-goals extraction)
  #:transparent)


(define/proof (done-refining term)
  (pure (refinement empty (lambda _ term))))

(define rule/c (-> sequent? (proof/c refinement?)))




