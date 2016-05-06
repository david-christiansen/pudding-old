#lang racket

(require (for-syntax syntax/parse racket/match
                     "infrastructure.rkt" "error-handling.rkt"
                     "proofs.rkt" "proof-state.rkt"))

(provide define/refiner)


(begin-for-syntax
  (struct definition (type extract renamer)
    #:property prop:rename-transformer (struct-field-index renamer)))

(define-syntax (define/refiner stx)
  (syntax-parse stx
    [(_ n:id type:expr script:expr ...)
     #'(begin
         (define-for-syntax extract
           (let ([completed (prove (new-goal type)
                                   (proof script ...))])
             (complete-proof-extract completed)))

         (define-syntax (get-extract stx) extract)

         (define runtime-extract (get-extract))

         (define-syntax n
           (definition
             #'type
             extract
             #'runtime-extract)))]))


