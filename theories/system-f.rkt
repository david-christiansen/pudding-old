#lang racket

(require syntax/parse (for-syntax syntax/parse))

(require "../error-handling.rkt" "../infrastructure.rkt")

(provide system-f)

(module+ test
  (require rackunit))

(define-namespace-anchor system-f)

;;; Syntax placeholders for judgments
(define-syntax (has-type stx) (raise-syntax-error #f "Judgment used out of context" stx))
(define-syntax (is-type stx) (raise-syntax-error #f "Judgment used out of context" stx))

(define ((is-the-identifier? x) y)
  (and (identifier? y)
       (free-identifier=? x y)))

(define-match-expander judgment
  (lambda (stx)
    (syntax-parse stx
      #:literals (has-type is-type)
      [(judgment (has-type ty))
       #'(app syntax->list
              (list (? (is-the-identifier? #'has-type))
                    ty))]
      [(judgment is-type)
       #'(? (is-the-identifier? #'is-type))]))
  (lambda (stx)
    (syntax-parse stx
      #:literals (has-type is-type)
      [(judgment (has-type ty))
       #'(quasisyntax/loc (has-type (unsyntax ty)) stx)]
      [(judgment is-type)
       #'(syntax is-type)])))


;;; Syntax placeholders for types
(define-syntax (Int stx)
  (raise-syntax-error #f "Type used out of context" stx))
(define-syntax (String stx)
  (raise-syntax-error #f "Type used out of context" stx))
(define-syntax (→ stx)
  (raise-syntax-error #f "Type used out of context" stx))
(define-syntax (∀ stx)
  (raise-syntax-error #f "Type used out of context" stx))

(define-match-expander type
  (lambda (stx)
    (syntax-parse stx
      #:literals (→ ∀ Int String)
      [(type (→ t1 t2))
       #'(app syntax->list
              (list (? (is-the-identifier? #'→)) t1 t2))]
      [(type (∀ x t))
       #'(app syntax->list (list (? (lambda (x) (free-identifier=? x #'∀))) (? identifier? x) t))]
      [(type Int)
       #'(? (lambda (stx) (and (identifier? stx)
                               (free-identifier=? stx #'Int))))]
      [(type String)
       #'(? (lambda (stx) (and (identifier? stx)
                               (free-identifier=? stx #'String))))]))
  (lambda (stx)
    (syntax-parse stx
      #:literals (→ ∀ Int String)
      [(type (→ t1 t2))
       #'(quasisyntax (→ (unsyntax t1) (unsyntax t2)))]
      [(type (∀ x:id t))
       #'(quasisyntax (∀ (unsyntax x) (unsyntax t)))]
      [(type Int)
       #'(syntax/loc Int stx)]
      [(type String)
       #'(syntax/loc String stx)])))

(module+ test
  (check-equal? (match #'is-type
                  [(judgment is-type)
                   #t]
                  [else #f])
                #t)
  (check-equal? (match #'(→ Int (→ String Int))
                  [(type (→ (type String) (type String)))
                   #f]
                  [(type (→ (type Int) (type (→ (type String) _))))
                   #t]
                  [else #f])
                #t)
  (check-equal? (match #'(∀ x (→ x x))
                  [(type (∀ x (type (→ y z))))
                   #:when (and (free-identifier=? x y)
                               (free-identifier=? y z))
                   #t]
                  [else #f])
                #t))

;;; Add scopes to a type
(define (add-type-scopes stx)
  (match stx
    [(type (∀ α t))
     (let ([new-scope (make-syntax-introducer)])
       (new-scope (type (∀ α (add-type-scopes t))) 'add))]
    [(type (→ t1 t2))
     (type (→ (add-type-scopes t1)
              (add-type-scopes t2)))]
    [other other]))

;;; Do two syntax objects represent the same type?
;;; Precondition: the types have been scoped using add-type-scopes, or
;;; built using the refiner
(define (type=? t1 t2 [env '()])
  (match* (t1 t2)
    [((type Int) (type Int))
     #t]
    [((type String) (type String))
     #t]
    [((type (→ τ1 τ2)) (type (→ σ1 σ2)))
     (and (type=? τ1 σ1 env)
          (type=? τ2 σ2 env))]
    [((type (∀ α t)) (type (∀ β s)))
     (type=? t s (cons (cons α β) env))]
    [((? identifier? α) (? identifier? β))
     (let ([seen (assoc α env bound-identifier=?)])
       (if seen
           (bound-identifier=? (cdr seen) β)
           (free-identifier=? α β)))]
    [(_ _) #f]))

(module+ test
  (check-equal?
   (type=? (add-type-scopes #'(∀ α (→ α α)))
           (add-type-scopes #'(∀ β (→ β β))))
   #t)
  (check-equal?
   (type=? (add-type-scopes #'(∀ α (→ α α)))
           (add-type-scopes #'(∀ β (→ β Int))))
   #f)
  (check-equal?
   (type=? (add-type-scopes #'(∀ α (→ ι α)))
           (add-type-scopes #'(∀ β (→ ι β))))
   #t))


;; Does hypothesis N provide evidence for a particular judgment?
(define (hypothesis-proves? hyp j)
  (match* (hyp j)
    [((judgment (has-type t1)) (judgment (has-type t2)))
     (type=? t1 t2)]
    [((judgment is-type) (judgment is-type))
     #t]
    [(_ _)
     #f]))

(define/contract (hypothesis num)
  (-> natural-number/c rule/c)
  (match-lambda
    [(hypothetical hypotheses goal)
     (if (< num (length hypotheses))
         (match-let ([(cons id hyp) (list-ref hypotheses num)])
           (if (hypothesis-proves? hyp goal)
               (done-refining id)
               (refinement-fail
                'hypothesis
                (>> hypotheses goal)
                (format "Invalid hypothesis: expected ~a, got ~a"
                        (syntax->datum goal)
                        (syntax->datum hyp)))))
         (refinement-fail
          'hypothesis
          (>> hypotheses goal)
          "Hypothesis out of bounds"))]
    [other (refinement-fail 'hypothesis
                            other
                            "not a well-formed goal")]))


;;; Rules for building types
(define/contract Int-f rule/c
  (match-lambda
    [(hypothetical _ (judgment is-type))
     (done-refining #'Int)]
    [other (refinement-fail 'Int-f
                            other
                            "wrong goal")]))

(define/contract String-f rule/c
  (match-lambda
    [(hypothetical _ (judgment is-type))
     (done-refining #'String)]
    [other (refinement-fail 'String-f
                            other
                            "wrong goal")]))

(define/contract Fun-f rule/c
  (match-lambda
    [(hypothetical hyps (judgment is-type))
     (success
      (refinement
       (list (relevant-subgoal (>> hyps (judgment is-type)))
             (relevant-subgoal (>> hyps (judgment is-type))))
       (lambda (dom cod)
         #`(→ #,dom #,cod))))]
    [other (refinement-fail 'String-f
                            other
                            "wrong goal")]))

(define/contract (Forall-f α)
  (-> symbol? rule/c)
  (match-lambda
    [(>> hyps (judgment is-type))
     (let* ([new-scope (make-syntax-introducer)]
            [annotated-name (new-scope (datum->syntax #f α) 'add)])
       (success
        (refinement (list (relevant-subgoal
                           (>> (cons (cons annotated-name
                                           (judgment is-type))
                                     hyps)
                               (judgment is-type))))
                    (lambda (ext)
                      (type (∀ annotated-name
                               (new-scope ext 'add)))))))]
    [other (refinement-fail 'Forall-f other "Goal must be type")]))



;;; Rules for programs
(define/contract (string-intro str)
  (-> string? rule/c)
  (match-lambda
    [(>> _ (type String))
     (done-refining (datum->syntax #'here str))]
    [other
     (refinement-fail 'string-intro other "Goal must be String")]))

(define/contract (int-intro i)
  (-> integer? rule/c)
  (match-lambda
    [(>> _ (type Int))
     (done-refining (datum->syntax #'here i))]
    [other
     (refinement-fail 'int-intro other "Goal must be Int")]))


(define/contract (function-intro x)
  (-> symbol? rule/c)
  (match-lambda
    [(>> hyps (type (→ τ σ)))
     (let* ([new-scope (make-syntax-introducer)]
            [annotated-name (new-scope (datum->syntax #f x) 'add)])
       (success (refinement (list (relevant-subgoal
                                   (>> (cons (cons annotated-name τ)
                                             hyps)
                                       σ)))
                            (lambda (extract)
                              #`(lambda (#,annotated-name)
                                  #,(new-scope extract 'add))))))]
    [other (refinement-fail 'function-intro other "Goal must be function type")]))


