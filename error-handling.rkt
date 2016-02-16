#lang racket

(require (for-syntax syntax/parse))

(provide all-success can-fail? let! match-let! match! with-fallbacks
         success/c failure/c can-fail/c
         (struct-out success)
         (struct-out failure))

(module+ test
  (require rackunit))

(struct success (value) #:transparent)
(struct failure (reason) #:transparent)

(define (can-fail? v) (or (success? v) (failure? v)))

(define ((success/c c) v) (and (success? v) (c (success-value v))))
(define ((failure/c c) v) (and (failure? v) (c (failure-reason v))))
(define (can-fail/c f s) (or/c (failure/c f) (success/c s)))

(define (bind val f)
  (if (success? val)
      (f (success-value val))
      val))

(begin-for-syntax
  (define-syntax-class failure-binding
    #:description "let! binding"
    (pattern (name:id computation:expr))))

(define-syntax (let! stx)
  (syntax-parse stx
    [(let! ()
       expr-or-def ... body:expr)
     #'(begin expr-or-def ... body)]
    [(let! (binding:failure-binding binds ...)
       expr-or-def ... body:expr)
     #'(bind binding.computation
             (lambda (binding.name)
               (let! (binds ...) expr-or-def ... body)))]))

(define-syntax (match-let! stx)
  (syntax-parse stx
    [(match-let! () body:expr)
     #'body]
    [(match-let! ([pattern computation] binds ...) body:expr)
     #'(bind computation
             (match-lambda [pattern (match-let! (binds ...) body)]))]))

(define-syntax (match! stx)
  (syntax-parse stx
    [(match! subject (pattern body-or-def ... body) ...)
     #'(match subject
         [(success pattern) body-or-def ... body] ...
         [(failure err) (failure err)]
         [other (raise-arguments-error 'match!
                                       "Not a success or failure"
                                       "subject" subject)])]))

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
            (fallbacks reason  (cons pred handler) ...)]
           [other
            (raise-arguments-error 'with-fallbacks
                                   "Not a success or failure"
                                   "result"
                                   other)]))]))


;;; TODO: make something better here, like for/success-list
(define (all-success lst)
  (if (null? lst)
      (success null)
      (let! ([head (car lst)]
             [tail (all-success (cdr lst))])
        (success (cons head tail)))))




(module+ test
  (test-begin
    (define (head lst)
      (if (cons? lst)
          (success (car lst))
          (failure "empty list")))

    (check-equal? (let! ([x (head '(1 2 3))]
                         [y (head '(3 4 5))])
                    (success (+ x y)))
                  (success 4))
    (check-equal? (let! ([x (head '(1 2 3))]
                         [y (head '())])
                    (success (+ x y)))
                  (failure "empty list"))
    (check-equal? (with-fallbacks ([false? (thunk* 1)] [string? string-length])
                    (let! ([x (head '(1 2 3))]
                           [y (head '())])
                      (success (+ x y))))
                  10)
    (check-equal? (match! (success 2) [1 "a"] [2 "b"] [3 "c"])
                  "b")
    (check-equal? (match! (failure 2) [1 "a"] [2 "b"] [3 "c"])
                  (failure 2))))
