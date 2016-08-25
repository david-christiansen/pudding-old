#lang racket

(require syntax/parse)
(require (for-syntax syntax/parse))
(require "../define-rule.rkt" "../infrastructure.rkt" "../error-handling.rkt" "../proof-state.rkt")
(require "../proofs.rkt")
(require (for-template racket/base))

(require "../expand-bindings.rkt")

(provide (all-defined-out) ;;TODO
         )

(require macro-debugger/stepper macro-debugger/syntax-browser)

;; Experimental generic substitution

(define/contract (subst bindings to-subst term)
  (-> bindings/c
      (listof (list/c identifier? syntax?))
      syntax?
      syntax?)
  (define (find i)
    (let loop ([todo to-subst])
      (match todo
        [(list) #f]
        [(cons (list (app get-occurrence-id id) val) more)
         #:when (and id (= id i))
         val]
        [(cons _ more) (loop more)])))
  (define (helper stx)
    (syntax-parse stx
      [x:id
       (define x-id (get-occurrence-id #'x))
       (match (assv x-id bindings)
         [`(,_ bound ,(? exact-nonnegative-integer? i))
          (define res (find i))
          (if res res #'x)]
         [_
          #'x])]
      [(e ...)
       (datum->syntax stx (map helper (syntax->list #'(e ...))))]
      ;; todo: cases for "exotic" structures in syntax
      [_ stx]))
  (helper term))

(define/contract (beta-reduction term)
  (-> syntax? syntax?)
  (define decorated (decorate-identifiers term))
  (define bindings (find-bindings (expand decorated)))
  (syntax-parse decorated
    [((lambda (x) body) arg)
     (subst bindings (list (list #'x #'arg)) #'body)]
    [_ (raise-argument-error 'beta-reduction "Beta-redex" term)]))

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

(define-syntax-class level
  #:attributes (level)
  (pattern lvl:nat
           #:attr level (syntax->datum #'lvl)))

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

;; Rules for the universe
(define (type-formation i)
  (rule #:literals (Type)
        (>> H (Type j))
        #:when (let ([j-lvl (syntax-e #'j)])
                 (and (exact-nonnegative-integer? j-lvl)
                      (< i j-lvl)))
        ()
        (Type #,(datum->syntax 'here i))))

(define type-equality
  (rule #:literals (Type =-in)
        (>> H (=-in (Type j1:level) (Type j2:level) (Type k:level)))
        #:when (and (= (attribute j1.level) (attribute j2.level))
                    (< (attribute j1.level) (attribute k.level)))
        ()
        (void)))

(define (cumulativity j)
  (rule #:literals (Type in)
        (>> H (in T (Type k:level)))
        #:when (< j (attribute k.level))
        ([_ (>> H (in T (Type #,j)))])
        (void)))

;; Rules for equality
(define-rule equality-symmetry
  #:literals (=-in)
  (>> H (=-in M N A))
  ([_ (>> H (=-in N M A))])
  (void))


;; Rules for absurdity
(define-rule absurd-formation
  #:literals (Type)
  (>> H (Type i:level))
  ()
  (Absurd))

(define-rule absurd-equality
  #:literals (=-in Absurd Type)
  (>> H (=-in (Absurd) (Absurd) (Type i:level)))
  #:when (exact-nonnegative-integer? (syntax-e #'i))
  ()
  (void))

(define-rule error-equality
  #:literals (=-in Absurd error)
  (>> H (=-in (error x) (error y) T))
  ([_ (>> H (=-in x y Absurd))])
  (void))



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
        (>> (at-hyp i H1 (hypothesis x (? parse-Absurd) _) H2) _)
        ()
        (error x)))

;; Rules for the unit type (here called Void)
(define void-formation
  (rule #:literals (Type)
        (>> H (Type i:level))
        ()
        (Void)))

(define-rule void-equality
  #:literals (=-in Void Type)
  (>> H (=-in (Void) (Void) (Type i:level)))
  #:when (exact-nonnegative-integer? (syntax-e #'i))
  ()
  (void))

(define-rule void-intro
  #:literals (Void)
  (>> H (Void))
  ()
  (void))

(define (parse-Void stx)
  (match (syntax-e stx)
    [(? identifier? id)
     (free-identifier=? id #'Void)]
    [_ #f]))

(define (void-elim i)
  (rule #:literals (Void)
        (>> (at-hyp i H1 (hypothesis x (? parse-Void) r?) H2)
            G)
        ([g (>> (append H1 (list (hypothesis x #'(Void) r?)) H2)
                G)])
        g))

(define-rule void-elem-eq
  #:literals (Void void)
  (>> H (=-in (void) (void) (Void)))
  ()
  (void))

;; Rules for Booleans
(define boolean-formation
  (rule #:literals (Type)
        (>> H (Type i:level))
        ()
        (Boolean)))

(define-rule boolean-equality
  #:literals (=-in Boolean Type)
  (>> H (=-in (Boolean) (Boolean) (Type i:level)))
  #:when (exact-nonnegative-integer? (syntax-e #'i))
  ()
  (void))

(define-rule boolean-intro-t
  #:literals (Boolean)
  (>> H (Boolean))
  ()
  #t)

(define-rule boolean-intro-f
  #:literals (Boolean)
  (>> H (Boolean))
  ()
  #f)

(define (stx-boolean? stx)
  (syntax-parse stx
    #:literals (Boolean)
    [(Boolean) #t]
    [_ #f]))

(define (boolean-elim i)
  (rule #:literals (Void)
        (>> (at-hyp i H1 (and h (hypothesis x (? stx-boolean?) r?)) H2)
            G)
        ;; TODO subst in H2, G
        ([t (>> (instantiate-hyps H2 x #'#t H1)
                G)]
         [f (>> (instantiate-hyps H2 x #'#f H1)
                G)])
        (if #,x t f)))

(define-rule boolean-elem-eq-t
  #:literals (Boolean)
  (>> H (=-in #t #t (Void)))
  ()
  (void))

(define-rule boolean-elem-eq-f
  #:literals (Boolean)
  (>> H (=-in #f #f (Void)))
  ()
  (void))


;; Rules for non-dependent functions
(define-rule function-formation
  #:literals (Type)
  (>> H (Type i:level))
  ([A (>> H (Type i))]
   [B (>> H (Type i))])
  (--> A B))

(define-rule function-equality
  #:literals (Type --> =-in)
  (>> H (=-in (--> A B) (--> C D) (Type i:level)))
  ([_ (>> H (=-in A C (Type i)))]
   [_ (>> H (=-in B D (Type i)))])
  (void))

(define (lambda-intro i x)
  (with-syntax ([i i] [x x])
    (rule #:literals (--> =-in Type)
          #:scopes (x-scope)
          (>> H (--> A B))
          ([body (>> (cons (hypothesis (x-scope #'x 'add)
                                       #'A
                                       #t)
                           H)
                     B)]
           [_ (>> H (=-in A A (Type i)))])
          (lambda (#,(x-scope #'x 'add)) body))))


(define-rule apply-reduce
  #:literals (lambda =-in)
  (>> H (=-in ((lambda (x) body) arg) res T))
  ([_ (>> H (=-in #,(beta-reduction #'((lambda (x) body) arg))
                  res
                  T))])
  (void))

(define-rule (function-extensionality [x name])
  #:literals (=-in -->)
  (>> H (=-in F G (--> A B)))
  ([_ (>> (cons (hypothesis #'x #'A #t) H)
          (=-in (F x) (G x) B))])
  (void))


(define dependent-function-formation
  (rule #:literals (Type)
        (>> H (Type i:level))
        ([A (>> H (Type i))]
         [B (A) (>> H (--> A (Type i)))])
        (Pi A B)))
