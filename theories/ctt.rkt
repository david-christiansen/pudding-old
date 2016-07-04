#lang racket

(require syntax/parse)
(require (for-syntax syntax/parse))
(require "../define-rule.rkt" "../infrastructure.rkt" "../error-handling.rkt" "../proof-state.rkt")
(require (for-template racket/base))

(require "../expand-bindings.rkt")

(provide (all-defined-out) ;;TODO
         )

;; Experimental generic substitution

(define/contract (subst context to-subst term)
  (-> (listof identifier?)
      (listof (list/c identifier? syntax?))
      syntax?
      syntax?)
  (define decorated
    (decorate-identifiers term))
  (define decorated-context
    (map decorate-identifiers context))
  (define decorated-to-subst
    (for/list ([todo to-subst])
      (match todo
        [(list id new)
         (define found (member id decorated-context))
         (list (if found
                   (car found)
                   (decorate-identifiers id))
               (decorate-identifiers new))])))
  (define bindings
    (find-bindings (expand decorated) context))
  (define (find i)
    (let loop ([todo decorated-to-subst])
      (cond [(null? todo)
             #f]
            [(let ([id (get-occurrence-id (caar todo))])
               (and id (= id i)))
             (cdar todo)]
            [else (loop (cdr todo))])))
  (define (helper stx)
    (syntax-parse stx
      [x:id
       (define x-id (get-occurrence-id #'x))
       (match (assv x-id bindings)
         [`(bound ,(? exact-nonnegative-integer? i))
          (define res (find i))
          (if res res #'x)]
         [_
          #'x])]
      [(e ...)
       (datum->syntax stx (map helper (syntax->list #'(e ...))))]
      ;; todo: cases for "exotic" structures in syntax
      [_ stx]))
  (helper term))

(define (instantiate-hyp before name val hyp)
  (match hyp
    [(hypothesis x t r?)
     (hypothesis x
                 (subst (map hypothesis-name before)
                        (list (list name val))
                        t)
                 r?)]))
(define (instantiate-hyps before name val after)
  (match after
    [(list) before]
    [(cons h hs)
     (instantiate-hyps
      (cons (instantiate-hyp before name val h)
            before)
      name
      val
      hs)]))


;; Base types for the universe
(struct Absurd () #:transparent)
(struct Void () #:transparent)
(struct Boolean () #:transparent)
(struct Nat () #:transparent)
(struct String () #:transparent)

;; Compound types for the universe
(struct --> (domain codomain) #:transparent)
(struct Either (A B) #:transparent)
(struct Pi (A B) #:transparent)
(struct Isect (over family) #:transparent)
(struct =-in (a b type) #:transparent)

(define (in a A)
  (=-in a a A))

;; For the predicative hierarchy
(struct Type (level) #:transparent)

(define-match-expander level
  (syntax-parser
    [(_ i)
     #'(? syntax?
         (app syntax-e
              (? exact-nonnegative-integer? i)))]))

;; Rules for the universe
(define (type-formation i)
  (rule #:literals (Type)
        [(>> H (Type j))
         #:when (let ([j-lvl (syntax-e #'j)])
                  (and (exact-nonnegative-integer? j-lvl)
                       (< i j-lvl)))
         ()
         (Type #,(datum->syntax 'here i))]))

(define type-equality
  (rule #:literals (Type =-in)
        [(>> H (=-in (Type j1) (Type j2) (Type k)))
         #:when (let ([j1-lvl (syntax-e #'j1)]
                      [j2-lvl (syntax-e #'j2)]
                      [k-lvl (syntax-e #'k)])
                  (and (exact-nonnegative-integer? j1-lvl)
                       (exact-nonnegative-integer? j2-lvl)
                       (exact-nonnegative-integer? k-lvl)
                       (= j1-lvl j2-lvl)
                       (< j1-lvl k-lvl)))
         ()
         (void)]))

(define (cumulativity j)
  (rule #:literals (Type in)
        [(>> H (in T (Type k)))
         #:when (let ([k-lvl (syntax-e #'k)])
                  (and (exact-nonnegative-integer? k-lvl)
                       (< j k-lvl)))
         ([_ (>> H (in T (Type #,j)))])
         (void)]))


;; Rules for absurdity
(define-rule absurd-formation
  #:literals (Type)
  [(>> H (Type i))
   ()
   (Absurd)])

(define-rule absurd-equality
  #:literals (=-in Absurd Type)
  [(>> H (=-in (Absurd) (Absurd) (Type i)))
   #:when (exact-nonnegative-integer? (syntax-e #'i))
   ()
   (void)])

(define-rule error-equality
  #:literals (=-in Absurd error)
  [(>> H (=-in (error x) (error y) T))
   ([_ (>> H (=-in Absurd x y))])
   (void)])

(define-match-expander at-hyp
  (syntax-parser
    [(_ i before this-hyp after)
     #'(? (lambda (H) (> (length H) i))
         (app (lambda (H) (split-at H i))
              before
              (cons this-hyp after)))]))

(define (parse-Absurd stx)
  (match (syntax-e stx)
    [(? identifier? id)
     (free-identifier=? id #'Absurd)]
    [_ #f]))

(define (absurd-elim i)
  (rule #:literals (Absurd)
        [(>> (at-hyp i H1 (hypothesis x (? parse-Absurd) _) H2) _)
         ()
         (error x)]))

;; Rules for the unit type (here called Void)
(define void-formation
  (rule #:literals (Type)
        [(>> H (Type i))
         ()
         (Void)]))

(define-rule void-equality
  #:literals (=-in Void Type)
  [(>> H (=-in (Void) (Void) (Type i)))
   #:when (exact-nonnegative-integer? (syntax-e #'i))
   ()
   (void)])

(define-rule void-intro
  #:literals (Void)
  [(>> H (Void))
   ()
   (void)])

(define (parse-Void stx)
  (match (syntax-e stx)
    [(? identifier? id)
     (free-identifier=? id #'Void)]
    [_ #f]))

(define (void-elim i)
  (rule #:literals (Void)
        [(>> (at-hyp i H1 (hypothesis x (? parse-Void) r?) H2)
             G)
         ([g (>> (append H1 (list (hypothesis x #'(Void) r?)) H2)
                 G)])
         g]))

(define-rule void-elem-eq
  #:literals (Void void)
  [(>> H (=-in (void) (void) (Void)))
   ()
   (void)])

;; Rules for Booleans
(define boolean-formation
  (rule #:literals (Type)
        [(>> H (Type i))
         ()
         (Boolean)]))

(define-rule boolean-equality
  #:literals (=-in Boolean Type)
  [(>> H (=-in (Boolean) (Boolean) (Type i)))
   #:when (exact-nonnegative-integer? (syntax-e #'i))
   ()
   (void)])

(define-rule boolean-intro-t
  #:literals (Boolean)
  [(>> H (Boolean))
   ()
   #t])

(define-rule boolean-intro-f
  #:literals (Boolean)
  [(>> H (Boolean))
   ()
   #f])

(define (parse-Boolean stx)
  (match (syntax-e stx)
    [(? identifier? id)
     (free-identifier=? id #'Boolean)]
    [_ #f]))

(define (boolean-elim i)
  (rule #:literals (Void)
        [(>> (at-hyp i H1 (hypothesis x (? parse-Boolean) r?) H2)
             G)
         ;; TODO subst in H2, G
         ([t (>> (instantiate-hyps H2 x #'#t H1)
                 G)]
          [f (>> (instantiate-hyps H2 x #'#f H1)
                 G)])
         (if #,x t f)]))

(define-rule boolean-elem-eq-t
  #:literals (Boolean)
  [(>> H (=-in #t #t (Void)))
   ()
   (void)])

(define-rule boolean-elem-eq-f
  #:literals (Boolean)
  [(>> H (=-in #f #f (Void)))
   ()
   (void)])


;; Rules for non-dependent functions
(define-rule function-formation
  #:literals (Type)
  [(>> H (Type i))
   ([A (>> H (Type i))]
    [B (>> H (Type i))])
   (--> A B)])

(define-rule function-equality
  #:literals (Type --> =-in)
  [(>> H (=-in (--> A B) (--> C D) (Type i)))
   ([_ (>> H (=-in A C (Type i)))]
    [_ (>> H (=-in B D (Type i)))])
   (void)])

(define (lambda-intro i x)
  (with-syntax ([i i] [x x])
    (rule #:literals (--> =-in Type)
          #:scopes (x-scope)
          [(>> H (--> A B))
           ([body (>> (cons (hypothesis (x-scope #'x 'add)
                                        #'A
                                        #t)
                            H)
                      B)]
            [_ (>> H (=-in S S (Type i)))])
           (lambda (#,(x-scope #'x 'add)) body)])))
