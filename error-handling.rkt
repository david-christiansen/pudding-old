#lang racket

(require (for-syntax syntax/parse)
         racket/stxparam
         "monad-notation.rkt")

(provide
 ;; Re-exported monad stuff
 pure <-
 ;; The proof monad
 proof
 proof-fail
 proof-run
 proof-eval
 proof-get proof-put proof-modify
 proof-chain-list
 define/proof
 for/proof/list
 for*/proof/list
 (struct-out success)
 (struct-out failure))

(module+ test
  (require rackunit))

;;; The proof monad is a state-and-error monad.  Values are functions
;;; that take a proof state and produce either a pair of a success
;;; value and a new state or a failure with an error.
;;;
;;; In other words, failure undoes any changes to the state.

(struct success (value state) #:transparent)
(struct failure (reason) #:transparent)

(define (proof-fail reason)
  (lambda (state)
    (failure reason)))

(define (proof-pure val)
  (lambda (state)
    (success val state)))

(define (proof-bind x k)
  (lambda (old-state)
    (match (x old-state)
      [(failure reason) (failure reason)]
      [(success val new-state)
       ((k val) new-state)])))

(struct exn:fail:not-exn exn:fail (reason)
  #:extra-constructor-name make-exn:fail:not-exn
  #:transparent)

(define (proof-run program state)
  (match (program state)
    [(success out new-state)
     (values out new-state)]
    [(failure reason)
     (if (exn? reason)
         (raise reason)
         (raise (make-exn:fail:not-exn
                 "Not an exception"
                 (current-continuation-marks) reason)))]))

(define (proof-eval program state)
  (call-with-values (thunk (proof-run program state))
                    (lambda (result new-state)
                      result)))


(module+ test
  (check-equal? ((proof-pure 3) (void))
                (success 3 (void)))
  (check-equal? ((proof-bind
                  (proof-pure 3)
                  (lambda (x)
                    (proof-bind
                     (proof-pure 2)
                     (lambda (y)
                       (proof-pure (+ x y))))))
                 (void))
                (success 5 (void))))


(define (proof-get state)
  (success state state))

(define (proof-put new-state)
  (lambda (old-state)
    (success (void) new-state)))

(module+ test
  (check-equal?
   ((proof-bind
     proof-get
     (lambda (x)
       (proof-bind
        (proof-put (+ x 1))
        (lambda (whatever)
          (proof-pure "done")))))
    0)
   (success "done" 1)))

(define-syntax (proof stx)
  (syntax-parse stx
    [(_ steps:expr ... last:expr)
     (syntax/loc stx
       (syntax-parameterize ([current-pure #'proof-pure])
         (do-impl proof-bind steps ... last)))]))

(module+ test
  (check-equal? (call-with-values
                 (thunk
                  (proof-run (proof
                              (<- x (pure 13))
                              (<- y (pure 23))
                              (<- s proof-get)
                              (proof-put (* s y))
                              (pure (+ x y)))
                             5))
                 list)
                (list 36 115)))

(define (proof-modify f)
  (proof (<- st proof-get)
         (proof-put (f st))))

(module+ test
  (check-equal? (call-with-values
                 (thunk (proof-run (proof (proof-modify add1)
                                          (proof-modify add1)
                                          (pure 7))
                                   2))
                 cons)
                (cons 7 4)))

(define-syntax (handle-errors stx)
  (syntax-parse stx
    [(_ program (handler-pattern rhs ...) ...)
     #'(lambda (old-state)
         (match (program old-state)
           [(success val new-state)
            (success val new-state)]
           [(failure reason)
            (match reason
              [handler-pattern ((proof rhs ...) old-state)]
              ...
              [other ((proof-fail other) old-state)])]))]))

(define-syntax (define/proof stx)
  (syntax-parse stx
    [(_ name:id body ... )
     #'(define name (proof body ...))]
    [(_ (name:id param:expr ...) body ...)
     #'(define (name param ...)
         (proof body ...))]))

(module+ test
  (define/proof (>5 x)
    (if (> x 5)
        (pure x)
        (proof-fail "No way")))
  (define/proof (tester x)
    (handle-errors (proof (<- y (>5 x))
                          (pure y))
                   ["No way" (proof-fail #f)]))
  (check-equal? ((tester 1) (void)) (failure #f))
  (check-equal? ((tester 5) (void)) (failure #f))
  (check-equal? ((tester 6) (void)) (success 6 (void))))

(define (proof-chain-list lst)
  (cond
    [(null? lst)
     (proof-pure lst)]
    [(pair? lst)
     (proof (<- hd (car lst))
            (<- tl (proof-chain-list (cdr lst)))
            (proof-pure (cons hd tl)))]))

(module+ test
  (check-equal? ((proof-chain-list (list (proof-pure 1)
                                         (proof-fail "no")
                                         (proof-pure 2)))
                 5)
                (failure "no"))
  (check-equal? ((proof-chain-list (list (proof-pure 1)
                                         (proof-pure 2)))
                 5)
                (success '(1 2) 5)))

(define (ap-proof proc arg)
  (proof (<- f proc)
         (<- x arg)
         (pure (f x))))

(define (ap-proof-2 proc arg1 arg2)
  (proof (<- f proc)
         (<- x arg1)
         (<- y arg2)
         (pure (f x y))))

(define ((lift-proof proc) arg)
  (proof (<- x arg)
         (pure (proc x))))

(define ((lift-proof-2 proc) arg1 arg2)
  (proof (<- x arg1)
         (<- y arg2)
         (pure (proc x y))))


(define-syntax (for/proof/list stx)
  (syntax-parse stx
    [(_ clauses steps ...)
     (with-syntax ([orig stx])
       #'(proof (<- backwards (for/fold/derived
                               orig ([acc (proof (pure '()))])
                               clauses
                               (proof (<- tl acc)
                                      (<- hd (proof steps ...))
                                      (pure (cons hd tl)))))
                (pure (reverse backwards))))]))

(module+ test
  (check-equal? (proof-eval (for/proof/list
                             ([x '(1 2 3 4 5)]
                              [y '(a b c d)])
                             (<- z proof-get)
                             (proof-put (* z 2))
                             (pure (list x y z)))
                            1)
                '((1 a 1) (2 b 2) (3 c 4) (4 d 8))))

(define-syntax (for*/proof/list stx)
  (syntax-parse stx
    [(_ clauses steps ...)
     (with-syntax ([orig stx])
         #'(proof (<- backwards (for*/fold/derived
                                 orig ([acc (proof (pure '()))])
                                 clauses
                                 (proof (<- tl acc)
                                        (<- hd (proof steps ...))
                                        (pure (cons hd tl)))))
                  (pure (reverse backwards))))]))

(module+ test
  (check-equal? (proof-eval (for*/proof/list
                             ([x '(1 2 3 4 5)]
                              [y '(a b c d)])
                             (<- z proof-get)
                             (proof-put (* z 2))
                             (pure (list x y z)))
                            1)
                '((1 a 1)     (1 b 2)      (1 c 4)      (1 d 8)
                  (2 a 16)    (2 b 32)     (2 c 64)     (2 d 128)
                  (3 a 256)   (3 b 512)    (3 c 1024)   (3 d 2048)
                  (4 a 4096)  (4 b 8192)   (4 c 16384)  (4 d 32768)
                  (5 a 65536) (5 b 131072) (5 c 262144) (5 d 524288))))
