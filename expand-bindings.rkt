#lang racket

(require syntax/parse)

(provide decorate-identifiers find-bindings get-occurrence-id)

(define my-id-prop 'binder-finder-identifer)

(define-syntax if-let
  (syntax-rules ()
    [(_ (x expr) a b)
     (let ([x expr])
       (if x a b))]))

(define (decorate-identifiers-in-cdr v)
  (cond
    [(null? v)
     '()]
    [(syntax? v)
     (decorate-identifiers v)]
    [(pair? v)
     (cons (decorate-identifiers (car v))
           (decorate-identifiers-in-cdr (cdr v)))]))

(define unique-id
  (let ([unique-counter -1])
    (thunk (set! unique-counter (add1 unique-counter))
           unique-counter)))

(define (decorate-identifiers stx)
  (if (identifier? stx)
      (if (syntax-property stx my-id-prop)
          stx
          (syntax-property stx my-id-prop (unique-id) #t))
      (let ([contents (syntax-e stx)])
        (displayln contents)
        (cond
          [(pair? contents)
           (datum->syntax stx (cons (decorate-identifiers (car contents))
                                    (decorate-identifiers-in-cdr (cdr contents))))]
          [(null? contents)
           stx]
          [(vector? contents)
           (datum->syntax stx (vector-map decorate-identifiers contents))]
          [(box? contents)
           (datum->syntax stx (box (decorate-identifiers (unbox contents))))]
                                        ;TODO prefab struct, hash table
          [else stx]))))

(define-syntax LAMBDA (syntax-rules () [(_ (x ...) body) (lambda (x ...) body)]))

(define/contract (get-occurrence-id id)
  (-> identifier? (or/c exact-nonnegative-integer? #f))
  (syntax-property id my-id-prop))

(define/contract (find-id id bindings)
  (-> identifier? (listof identifier?) (or/c #f exact-nonnegative-integer?))
  (define mem (member id bindings bound-identifier=?))
  (and mem
       (syntax-property (car mem) my-id-prop)))

;;; Return a mapping from internal identifier IDs to either `(bound
;;; ,ID) if it is bound by ID, `(bound #f) if it is bound by something
;;; not in the source, or `(free) if it is not bound in the expansion,
;;; or `(binding) if it's a binding site.
;;;
;;; bindings is a list of identifiers bound in this scope.
(define/contract (find-bindings stx [bindings '()])
  (->* (syntax?)
       ((listof identifier?))
       (listof (cons/c exact-nonnegative-integer?
                       (or/c (list/c 'bound exact-nonnegative-integer?)
                             (list/c 'bound #f)
                             (list/c 'free)
                             (list/c 'binding)))))
  (define (under-bindings formals body)
    (let* ([bs (if (identifier? formals)
                   (list formals)
                   (syntax->list formals))]
           [bound-ids
            (reverse
             (for/list ([x bs])
               (cons x (syntax-property x my-id-prop))))])
      (apply append
             (for/list ([x bound-ids]
                        #:when (cdr x))
               `(,(cdr x) binding))
             (for/list ([b body])
               (find-bindings b (append (reverse bs) bindings))))))
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    ;; top-level forms
    [(#%expression expr)
     (find-bindings #'expr bindings)]
    [(module m:id p (#%plain-module-begin form ...))
     (apply append
            (map (lambda (e) (find-bindings e bindings))
                 (syntax->list #'(form ...))))]
    [(begin-for-syntax form ...)
     (apply append
            (map (lambda (e) (find-bindings e bindings))
                 (syntax->list #'(form ...))))]

    ;; module-level forms
    [(#%provide spec ...) '()]
    [(#%declare e ...) '()]

    ;; submodules
    [(module* m:id p (#%plain-module-begin form ...))
     (apply append find-bindings (syntax->list #'(form ...)))]

    ;; top-level
    [(define-values form ...) (error "No support for defines yet")]
    [(define-syntaxes form ...) (error "No support for defines yet")]
    [(#%require form ...) '()]

    ;; expressions
    [(#%plain-lambda formals body0 body ...)
     (under-bindings #'formals (syntax->list #'(body0 body ...)))]
    [(case-lambda [formals body0 body ...] ...)
     (apply append (for/list ([this-case (syntax->list #'([formals body0 body ...] ...))])
                     (define here (syntax->list this-case))
                     (define formals (car here))
                     (define body (cdr here))
                     (under-bindings formals body)))]
    [(if e1 e2 e3)
     (append (find-bindings #'e1 bindings)
             (find-bindings #'e2 bindings)
             (find-bindings #'e3 bindings))]
    [(begin e ...)
     (apply append (map (lambda (e) (find-bindings e bindings))
                        (syntax->list #'(e ...))))]
    [(begin0 e ...)
     (apply append (map (lambda (e) (find-bindings e bindings))
                        (syntax->list #'(e ...))))]
    [(let-values ([(x ...) e] ...) body ...)
     (append
      (apply append (map (lambda (e) (find-bindings e bindings))
                         (syntax->list #'(e ...))))
      (under-bindings #'(x ... ...) (syntax->list #'(body ...))))]
    [(letrec-values ([(x ...) e] ...) body ...)
     (define in-scope (append (syntax->list #'(e ...)) (syntax->list #'(body ...))))
     (under-bindings #'(x ... ...) in-scope)]
    [(set! x e)
     (append (find-bindings #'set! bindings)
             (find-bindings #'x bindings)
             (find-bindings #'e bindings))]
    [(quote d) '()]
    [(quote-syntax dat)
     (find-bindings #'dat bindings)]
    [(quote-syntax dat #:local)
     (find-bindings #'dat bindings)]
    [(with-continuation-mark e1 e2 e3)
     (append (find-bindings #'e1 bindings)
             (find-bindings #'e2 bindings)
             (find-bindings #'e3 bindings))]
    [(#%plain-app expr ...)
     (apply append
            (for/list ([e (syntax->list #'(expr ...))])
              (find-bindings e bindings)))]
    [(#%top . id)
     (if-let (my-id (syntax-property #'id my-id-prop))
             (list `(,my-id free))
             '())]
    [(#%variable-reference id)
     (find-bindings #'id bindings)]
    [(#%variable-reference (#%top . id))
     (if-let (my-id (syntax-property #'id my-id-prop))
             (list `(,my-id free))
             '())]
    [(#%variable-reference) '()]
    [other
     #:when (identifier? #'other)
     (if-let (my-id (syntax-property #'other my-id-prop))
             (if-let (b (find-id #'other bindings))
                     (list `(,my-id bound ,b))
                     (list `(,my-id free)))
             '())]
    [other #;(error "unknown case" #'other)
           '()]))

(define foo #'(LAMBDA (x) (+ x x)))
(define my-x #'x)
(define bar (decorate-identifiers foo))
(define xx (decorate-identifiers my-x))



