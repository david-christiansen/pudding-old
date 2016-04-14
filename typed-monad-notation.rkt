#lang typed/racket

(require (for-syntax racket syntax/parse)
         "monad-notation-parameters.rkt"
         racket/stxparam)

(provide do-impl define-do current-monad current-pure pure <-)

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
  (define-syntax-class typed-bind
    #:literals (<- :)
    #:description "typed bind expression"
    (pattern (<- pattern:expr : type:expr term:expr)))
  (define-syntax-class do-let
    #:literals (let)
    #:description "let in do"
    (pattern (let pattern:expr term:expr)))
  (define-syntax-class do-typed-let
    #:literals (let :)
    #:description "typed let in do"
    (pattern (let pattern:expr : type:expr term:expr))))


(define-syntax (do-impl stx)
  (syntax-parse stx
    [(_ bind-op done:expr)
     (syntax/loc done done)]
    [(_ bind-op to-bind:bind body:expr ...)
     (syntax/loc (syntax to-bind)
       (bind-op to-bind.term
                (match-lambda
                  [to-bind.pattern (do-impl bind-op body ...)])))]
    [(_ bind-op to-bind:typed-bind body:expr ...)
     (let ([m (syntax-parameter-value #'current-monad)])
       (quasisyntax/loc (syntax to-bind)
         (bind-op (ann to-bind.term  (#,m to-bind.type))
                  (lambda ([x : to-bind.type])
                    (match x
                      [to-bind.pattern (do-impl bind-op body ...)])))))]
    [(_ bind-op to-let:do-typed-let body:expr ...)
     (quasisyntax/loc (syntax to-let)
       (match-let ([to-let.pattern (ann to-let.term to-let.type)])
         (do-impl bind-op body ...)))]
    [(_ bind-op to-let:do-let body:expr ...)
     (quasisyntax/loc (syntax to-let)
       (match-let ([to-let.pattern to-let.term])
         (do-impl bind-op body ...)))]
    [(_ bind-op first:expr rest:expr ...)
     (let ([m (syntax-parameter-value #'current-monad)])
       (quasisyntax/loc (syntax first)
         (bind-op (ann first (#,m Void))
                  (lambda ([ignored : Void])
                    (do-impl bind-op rest ...)))))]))

(define-syntax (define-do stx)
  (syntax-parse stx
    [(_ kwd:id monad:expr bind:expr pure-op:expr)
     #'(define-syntax (kwd inner)
         (syntax-parse inner
           [(_ x:expr (... ...))
            #'(syntax-parameterize ([current-monad
                                     #'monad]
                                    [current-pure
                                     #'pure-op])
               (do-impl bind x (... ...)))]))]))

(module+ test
  ;;; WARNING: not really a monad, oh well
  (: option->>= (All (A B)
                  (-> (Option A)
                      (-> A (Option B))
                      (Option B))))
  (define (option->>= val fun)
    (if val
        (fun val)
        #f))

  (define-do option-do Option option->>= identity)

  (check-equal? (option-do
                  (<- x : Number 40)
                  (<- y : Number #f)
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
                  (<- (list x y z) : (Listof Natural) (list 1 2 3))
                  (identity y))
                2)

  (define-type (State S) (All (A) (-> S (List A S))))

  (: get (All (S) (-> ((State S) S))))
  (define ((get) s) (list s s))

  (: put (All (S) (-> S ((State S) Void))))
  (define ((put new) old)
    (list (void) new))


  (: state-pure (All (S A) (-> A ((State S) A))))
  (define ((state-pure x) s) (list x s))

  (: skip (All (S) (-> ((State S) Void))))
  (define (skip) (state-pure (void)))

  (: state->>= (All (S A B)
                    (-> ((State S) A)
                        (-> A ((State S) B))
                        ((State S) B))))
  (define (state->>= val k)
    (lambda (state-1)
      (match-let ([(list x state-2) (val state-1)])
        ((k x) state-2))))

  (define-syntax (state-do stx)
    (syntax-parse stx
      [(_ state-type:expr steps:expr ... last:expr)
       (syntax/loc stx (syntax-parameterize ([current-monad #'(State state-type)]
                                             [current-pure #'state-pure])
                          (do-impl state->>= steps ... last)))]))
  
  (: modify (All (S) (-> (-> S S) ((State S) Void))))
  (define (modify f)
    (state->>= ((inst get S))
               (lambda ([x : S])
                 ((inst put S) (f x)))))

  (: modify2 (All (S) (-> (-> S S) ((State S) Void))))
  (define (modify2 f)
    (state-do S
              (<- s : S (get))
              (put s)))
  
  (: sum-string-lengths (-> (Rec A (U Null String (Pair A A)))
                            ((State Integer) Void)))
  (define (sum-string-lengths expr)
    (cond
      [(null? expr) (skip)]
      [(string? expr)
       (modify (lambda ([x : Integer]) (+ x (string-length expr))))]
      [(pair? expr)
       (state-do Integer
         (sum-string-lengths (car expr))
         (sum-string-lengths (cdr expr)))]))

  (check-equal? (cadr ((sum-string-lengths '((("hey" "you") "it's" ("a")) "string")) 0))
                17)
  
  (struct (A) success ([value : A]) #:transparent)
  (struct (E) failure ([error : E]) #:transparent)
  (define-type (Error E) (All (A) (U (failure E) (success A))))

  (: error->>= (All (E A B) (-> ((Error E) A)
                                (-> A ((Error E) B))
                                ((Error E) B))))
  (define (error->>= v k)
    (if (failure? v)
        v
        (k (success-value v))))

  (define-syntax (error-do stx)
    (syntax-parse stx
      [(_ error-type:expr steps:expr ... last:expr)
       (syntax/loc stx (syntax-parameterize ([current-monad #'(Error error-type)]
                                             [current-pure #'success])
                          (do-impl error->>= steps ... last)))]))

  (: all-success (All (E A) (-> (Listof ((Error E) A))
                                ((Error E) (Listof A)))))
  (define (all-success lst)
    (match lst
      [(cons x xs)
       (error-do E
         (<- hd : A x)
         (<- tl : (Listof A) (all-success xs))
         (pure (cons hd tl)))]
      [null
       (success '())]))

  (check-equal? (all-success (list (success 14) (success "hi") (success empty)))
                (success (list 14 "hi" empty)))
  (check-equal? (all-success (list (success 14) (failure "no way") (success empty)))
                (failure "no way"))

  (: with-a-let (Option String))
  (define with-a-let
     (option-do
       (<- x : String "hi")
       (let foo #f)
       (<- y : String "fnord")
       (pure (string-append x y))))
  (check-equal? with-a-let "hifnord")
)
;; Local Variables:
;; eval: (put (quote All) (quote racket-indent-function) 1)
;; eval: (put (quote option-do) (quote racket-indent-function) 0)
;; End:
