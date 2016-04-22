#lang racket

(require (for-syntax racket syntax/parse)
         (only-in "monad-notation-parameters.rkt" current-pure <-)
         racket/stxparam)

(provide do-impl define-do current-pure pure <-)

(module+ test (require typed/rackunit))

(define-syntax (pure stx)
  (let ([pure-op (syntax-parameter-value #'current-pure)])
    (syntax-parse stx
      [(_ arg)
       (quasisyntax/loc stx
         (#,pure-op arg))])))

(begin-for-syntax
  (define-syntax-class bind
    #:literals (<-)
    #:description "bind expression"
    (pattern (<- pattern:expr term:expr)))
  (define-syntax-class do-let
    #:literals (let)
    #:description "let in do"
    (pattern (let pattern:expr term:expr)))
  (define-syntax-class do-let-values
    #:literals (let-values)
    #:description "let-values in do"
    (pattern (let-values (patterns:expr ...) term:expr))))


(define-syntax (do-impl stx)
  (syntax-parse stx
    [(_ bind-op done:expr)
     (syntax/loc done done)]
    [(_ bind-op to-bind:bind body:expr ...)
     (syntax/loc (syntax to-bind)
       (bind-op to-bind.term
                (match-lambda
                  [to-bind.pattern (do-impl bind-op body ...)])))]
    [(_ bind-op to-let:do-let body:expr ...)
     (quasisyntax/loc (syntax to-let)
       (match-let ([to-let.pattern to-let.term])
         (do-impl bind-op body ...)))]
    [(_ bind-op to-let:do-let-values body:expr ...)
     (quasisyntax/loc (syntax to-let)
       (match-let-values ([(to-let.patterns ...) to-let.term])
         (do-impl bind-op body ...)))]
    [(_ bind-op first:expr rest:expr ...)
     (quasisyntax/loc (syntax first)
       (bind-op first
                (lambda (ignored)
                  (do-impl bind-op rest ...))))]))

(define-syntax (define-do stx)
  (syntax-parse stx
    [(_ kwd:id monad:expr bind:expr pure-op:expr)
     #'(define-syntax (kwd inner)
         (syntax-parse inner
           [(_ x:expr (... ...))
            #'(syntax-parameterize ([current-pure
                                     #'pure-op])
               (do-impl bind x (... ...)))]))]))

(module+ test
  ;;; WARNING: not really a monad, oh well
  (define (option->>= val fun)
    (if val
        (fun val)
        #f))

  (define-do option-do Option option->>= identity)

  (check-equal? (option-do
                  (<- x 40)
                  (<- y #f)
                  (+ x y))
                #f)

  (check-equal? (option-do (<- x 40)
                           x)
                40)

  (check-equal? (option-do (<- x 40)
                           (<- y "hello")
                           (box "hi"))
                (box "hi"))

  (check-equal? (option-do
                  (<- (list x y z) (list 1 2 3))
                  (identity y))
                2)

  (define ((get) s) (list s s))

  (define ((put new) old)
    (list (void) new))


  (define ((state-pure x) s) (list x s))

  (define (skip) (state-pure (void)))

  (define (state->>= val k)
    (lambda (state-1)
      (match-let ([(list x state-2) (val state-1)])
        ((k x) state-2))))

  (define-syntax (state-do stx)
    (syntax-parse stx
      [(_ state-type:expr steps:expr ... last:expr)
       (syntax/loc stx (syntax-parameterize ([current-pure #'state-pure])
                          (do-impl state->>= steps ... last)))]))

  (define (modify f)
    (state->>= (get)
               (lambda (x)
                 (put (f x)))))

  (define (modify2 f)
    (state-do S
              (<- s (get))
              (put s)))

  (define (sum-string-lengths expr)
    (cond
      [(null? expr) (skip)]
      [(string? expr)
       (modify (lambda (x) (+ x (string-length expr))))]
      [(pair? expr)
       (state-do Integer
         (sum-string-lengths (car expr))
         (sum-string-lengths (cdr expr)))]))

  (check-equal? (cadr ((sum-string-lengths '((("hey" "you") "it's" ("a")) "string")) 0))
                17)

  (struct success (value) #:transparent)
  (struct failure (error) #:transparent)

  (define (error->>= v k)
    (if (failure? v)
        v
        (k (success-value v))))

  (define-syntax (error-do stx)
    (syntax-parse stx
      [(_ error-type:expr steps:expr ... last:expr)
       (syntax/loc stx (syntax-parameterize ([current-pure #'success])
                          (do-impl error->>= steps ... last)))]))

  (define (all-success lst)
    (match lst
      [(cons x xs)
       (error-do E
         (<- hd x)
         (<- tl (all-success xs))
         (pure (cons hd tl)))]
      [null
       (success '())]))

  (check-equal? (all-success (list (success 14) (success "hi") (success empty)))
                (success (list 14 "hi" empty)))
  (check-equal? (all-success (list (success 14) (failure "no way") (success empty)))
                (failure "no way"))

  (define with-a-let
     (option-do
       (<- x "hi")
       (let foo #f)
       (<- y "fnord")
       (pure (string-append x y))))
  (check-equal? with-a-let "hifnord")
)
;; Local Variables:
;; eval: (put (quote All) (quote racket-indent-function) 1)
;; eval: (put (quote option-do) (quote racket-indent-function) 0)
;; End:
