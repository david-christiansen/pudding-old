#lang racket

(require (for-syntax syntax/parse))
(provide define-resource)

(module+ test (require rackunit))

;;;; Resources, inspired by MetaPRL but not identical to it

(define-syntax (define-resource stx)
  (syntax-parse stx
    [(_ r:id
        (~optional combiner:expr
                   #:defaults ([combiner #'identity]))
        (~optional (~seq #:contract elem-contract:expr)
                   #:defaults ([elem-contract #'any/c])))
     #'(define r
         (let ([param (make-parameter null)])
           ;; WARNING: Hack - using the same name for the internal
           ;; adder causes the blame messages to make sense, but there
           ;; must be a better way...
           (define/contract (r new-val)
             (-> elem-contract any/c)
             (cons new-val (param)))
           (make-derived-parameter
            param
            r
            combiner)))]))

(module+ test
  (define-resource elim-rules
    (lambda (xs) (apply string-append xs))
    #:contract string?)
  (check-equal? (elim-rules) "")
  (check-true (void? (elim-rules "hello")))
  (check-equal? (elim-rules) "hello")
  (check-true (void? (elim-rules "garbage")))
  (check-equal? (elim-rules) "garbagehello")
  (check-equal?
   (parameterize ([elim-rules "nope"])
     (elim-rules))
   "nopegarbagehello")
  (check-equal? (elim-rules) "garbagehello")

  (module defines-resource racket
    (require (submod ".." ".."))
    (provide flavors)
    (define-resource flavors reverse #:contract symbol?))

  (module light-flavors racket
    (require (submod ".." defines-resource))
    (flavors 'vanilla)
    (flavors 'tapioca))

  (module dark-flavors racket
    (require (submod ".." defines-resource))
    (flavors 'chocolate)
    (flavors 'devils-food)))

