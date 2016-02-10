#lang racket

(require (for-syntax syntax/parse racket/match "infrastructure.rkt"))

(provide define/refiner)


(begin-for-syntax
  (struct definition (type extract renamer)
    #:property prop:rename-transformer (struct-field-index renamer)))

(define-syntax (define/refiner stx)
  (syntax-parse stx
    [(_ n:id type:expr script:expr)
     #'(begin
         (define-for-syntax extract
           (match (script (new-goal #'type))
             [(refinement (list) ext) (ext)]
             [(refinement (cons goal goals) _)
              (raise-syntax-error 'define/refiner "Unsolved goal" script)]
             [_ (raise-syntax-error 'define/refiner "The impossible happened")]))

         (define-syntax (get-extract stx) extract)

         (define runtime-extract (get-extract))

         (define-syntax n
           (definition
             #'type
             extract
             #'runtime-extract)))]))


