#lang racket

(require (for-syntax syntax/parse)
         racket/stxparam
         "monad-notation.rkt")

(provide all-success pure error-do <- with-fallbacks
         (struct-out success)
         (struct-out failure))

(module+ test
  (require rackunit))

(struct success (value) #:transparent)
(struct failure (reason) #:transparent)

(define (err-bind val f)
  (if (success? val)
      (f (success-value val))
      val))

(define-syntax (error-do stx)
  (syntax-parse stx
    [(_ error-type:expr steps:expr ... last:expr)
     (syntax/loc stx
       (syntax-parameterize ([current-monad #'(Err error-type)]
                             [current-pure #'success])
         (do-impl err-bind steps ... last)))]))


(define (fallbacks failure-reason . handlers)
  (cond [(null? handlers)
         (raise-arguments-error 'with-fallbacks
                                "No fallback procedure for failure"
                                "failure" failure)]
        [((caar handlers) failure-reason)
         ((cdar handlers) failure-reason)]
        [else (apply fallbacks failure-reason (cdr handlers))]))

(define-syntax (with-fallbacks stx)
  (syntax-parse stx
    [(with-fallbacks ([pred handler] ...) body ...)
     #'(let ([res (begin body ...)])
         (match res
           [(success val) val]
           [(failure reason)
            (fallbacks reason (cons pred handler) ...)]
           [other
            (raise-arguments-error 'with-fallbacks
                                   "Not a success or failure"
                                   "result"
                                   other)]))]))


;;; TODO: make something better here, like for/success-list
(define (all-success lst)
  (if (null? lst)
      (success '())
      (error-do E
        (<- head (car lst))
        (<- tail (all-success (cdr lst)))
        (pure (cons head tail)))))


(module+ test
  (test-begin
    (define (head lst)
      (if (cons? lst)
          (success (car lst))
          (failure "empty list")))

    (check-equal? (error-do String
                    (<- x (head (list 1 2 3)))
                    (<- y (head (list 3 4 5)))
                    (success (+ x y)))
                  (success 4))
    (check-equal? (error-do String
                    (<- x (head '(1 2 3)))
                    (<- y (head '()))
                    (success (+ x y)))
                  (failure "empty list"))
    (check-equal? (with-fallbacks ([false? (lambda (_) 1)] [string? string-length])
                    (error-do String
                        (<- x (head '(1 2 3)))
                        (<- y (head '()))
                      (success (+ x y))))
                  10)))
