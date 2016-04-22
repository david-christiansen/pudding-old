#lang racket

(provide
 context-with-variable/c
 context-with-instantiated-variable/c
 context-with-uninstantiated-variable/c
 (contract-out [metavariable?
                (-> any/c boolean?)]
               [uninstantiated?
                (-> any/c boolean?)]
               [instantiated?
                (-> any/c boolean?)]
               [metavariable-context?
                (-> any/c boolean?)]
               [fresh-context
                (-> metavariable-context?)]
               [new-metavariable
                (-> metavariable-context?
                    symbol?
                    (values metavariable-context?
                            metavariable?))]
               [lookup-metavariable
                (->i ([context (x) (context-with-variable/c x)]
                      [x metavariable?])
                     [result (or/c uninstantiated? syntax?)])]
               [assign
                (->i ([x metavariable?]
                      [val syntax?]
                      [context (x)
                               (context-with-uninstantiated-variable/c x)])
                     [result (x)
                             (context-with-instantiated-variable/c x)])]
               [syntax-contains-metavariable?
                (-> syntax? boolean?)]
               [instantiate-metavariables
                (-> metavariable-context? syntax? syntax?)]))

(module+ test
  (require rackunit))



;;; A metavariable is a newtype wrapper around symbols
(struct metavariable (name)
  #:methods gen:custom-write
  [(define (write-proc metavar port mode)
     (write-string "‹" port)
     (write-string (symbol->string (metavariable-name metavar)) port)
     (write-string "›" port))])

(module+ test
  ;; Two metavariables with the same symbol should not be equal?
  (check-not-equal? (metavariable 'x) (metavariable 'x))

  ;; Equality of metavars should be reflexive
  (let ([x (metavariable 'x)])
    (check-equal? x x))

  ;; Output surrounds the metavar name in single guillemets
  (check-equal? (with-output-to-string
                  (thunk (print (metavariable 'x′))))
                "‹x′›"))

;;; The value of a metavariable that exists but has no value yet
(struct uninstantiated ()
  #:transparent)

(define (instantiated? x)
  (not (uninstantiated? x)))

(module+ test
  ;; All uninstantiated things are equivalent
  (check-equal? (uninstantiated) (uninstantiated))

  (check-equal? (instantiated? (uninstantiated)) #f))

;;; A metavariable context contains a collection of variables.  This
;;; is basically just a newtype wrapper.  The field display-names
;;; keeps track of what's already been used for user views.
(struct metavariable-context (variables display-names))

;;; Allocate a fresh metavariable context
(define (fresh-context)
  (metavariable-context (make-immutable-hasheq) (seteqv)))

(define (next-symbol sym)
  (string->symbol (string-append (symbol->string sym) "′")))

;;; Add a metavariable to a context. Return both.
(define (new-metavariable context x)
  (let* ([used-names (metavariable-context-display-names context)]
         [var (metavariable
               (let loop ()
                 (if (set-member? used-names x)
                     (begin (set! x (next-symbol x))
                            (loop))
                     x)))])
    (values (metavariable-context
             (hash-set (metavariable-context-variables context)
                       var
                       (uninstantiated))
             (set-add used-names x))
            var)))

(module+ test
  ;; Adding a metavariable twice yields distinct names
  (let ([Δ (fresh-context)])
    (let*-values ([(Δ′ x) (new-metavariable Δ 'x)]
                  [(Δ′′ x′) (new-metavariable Δ′ 'x)])
      (check-eqv? (metavariable-name x) 'x)
      (check-eqv? (metavariable-name x′) 'x′)
      (check-not-equal? x x′))))

(define ((context-with-variable/c x) context)
  (if (hash-ref (metavariable-context-variables context) x #f)
      #t
      #f))

(define ((context-with-uninstantiated-variable/c x) context)
  (let ([val (hash-ref (metavariable-context-variables context) x #f)])
    (and val (uninstantiated? val))))

(define ((context-with-instantiated-variable/c x) context)
  (let ([val (hash-ref (metavariable-context-variables context) x #f)])
      (and val (not (uninstantiated? val)))))


(define (lookup-metavariable context x)
  (hash-ref (metavariable-context-variables context) x))

(define (assign x val context)
  (let* ([variables (metavariable-context-variables context)]
         [used-names (metavariable-context-display-names context)])
    (metavariable-context (hash-set variables x val) used-names)))

(module+ test
  (test-case "Metavariable instantiation"
    (define a-context (fresh-context))
    (define-values (another-context x) (new-metavariable a-context 'x))

    (check-equal? (instantiated? (lookup-metavariable another-context x))
                  #f)

    (define-values (another-context-again y) (new-metavariable another-context 'y))

    (check-not-equal? x y)

    (define x-def-context (assign x #'42 another-context))

    (check-equal? (instantiated? (lookup-metavariable x-def-context x))
                  #t)

    (check-equal? (syntax-e (lookup-metavariable x-def-context x)) 42)))


(define (syntax-contains-metavariable? stx)
  (let ([contents (syntax-e stx)])
    (if (metavariable? contents)
        #t
        (match contents
          [(? list? xs)
           (ormap syntax-contains-metavariable? xs)]
          [(box x) (syntax-contains-metavariable? x)]
          [(? vector? (app vector->list (list-rest xs)))
           (ormap syntax-contains-metavariable? xs)]
          [_ #f]))))

(module+ test
  (check-equal? (syntax-contains-metavariable? #'(foo bar baz)) #f)
  (check-equal? (syntax-contains-metavariable? #`(foo #,(metavariable 'bar) baz)) #t))

(define (instantiate-metavariables context stx)
  (let ([contents (syntax-e stx)])
    (if (metavariable? contents)
        (let ([value (lookup-metavariable context contents)])
          (if (instantiated? value)
              value
              stx))
        (match contents
          [(? list? xs)
           (datum->syntax stx
                          (map (lambda (s)
                                 (instantiate-metavariables context s))
                               xs)
                          stx
                          stx)]
          [(box x)
           (datum->syntax stx (box (instantiate-metavariables context x)) stx stx)]
          [(? vector? v)
           (datum->syntax stx
                          (vector-map (lambda (s)
                                        (instantiate-metavariables context s))
                                      v)
                          stx
                          stx)]
          [other other]))))


(module+ test
  (test-case "Metavariable instantiation"
    (let ([stx #'(hello (this (is syntactic) #(stuff)))])
      (check-equal? (syntax->datum (instantiate-metavariables (fresh-context) stx))
                    (syntax->datum stx)))
    (define ctx-1 (fresh-context))
    (define-values (ctx-2 x) (new-metavariable ctx-1 'x))
    (define-values (ctx-3 x′) (new-metavariable ctx-2 'x))
    (define term #`(+ #,x 1 #,x′ 42))
    (check-equal? (syntax->datum term)
                  (syntax->datum (instantiate-metavariables ctx-3 term)))

    (define ctx-4 (assign x′ #'17 ctx-3))
    (check-equal? (syntax->datum #`(+ #,x 1 17 42))
                  (syntax->datum (instantiate-metavariables ctx-4 term)))

    (define ctx-5 (assign x #'(string-length "hi") ctx-4))
    (check-equal? (syntax->datum #`(+ (string-length "hi") 1 17 42))
                  (syntax->datum (instantiate-metavariables ctx-5 term)))))
