#lang racket

(require syntax/parse (for-syntax syntax/parse))

(require "../error-handling.rkt" "../infrastructure.rkt" "../proof-state.rkt" "../proofs.rkt")

(require (for-template racket/base racket/match))


(provide judgment has-type is-type
         type Int String → ∀
         add-type-scopes
         ;; Structural rules
         assumption
         ;; Formation rules
         Int-f String-f Fun-f Forall-f
         ;; Introduction rules
         string-intro int-intro function-intro
         Forall-intro
         ;; Elimination rules
         application)

(module+ test
  (require rackunit))

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
       #`(quasisyntax (has-type (unsyntax ty)))]
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
       #'(app syntax->list (list (? (lambda (id) (free-identifier=? id #'∀)))
                                 (? identifier? x)
                                 t))]
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
       #'(syntax Int)]
      [(type String)
       #'(syntax String)])))

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
    [((type (→ τ₁ τ₂)) (type (→ σ₁ σ₂)))
     (and (type=? τ₁ σ₁ env)
          (type=? τ₂ σ₂ env))]
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

(define/proof (refinement-fail rule-name goal message)
  (proof-fail (make-exn:fail (format "~a: Can't refine ~a. ~s"
                                     rule-name
                                     goal
                                     message)
                             (current-continuation-marks))))

(define (subgoals . goals)
  (for/proof/list ([x (in-cycle '(a b c d e f g h i j k l m n o
                                    p q r s t u v w x y z æ ø å))]
                   [g goals])
    (<- meta (new-meta x))
    (pure (subgoal meta g))))


;; Does hypothesis N provide evidence for a particular judgment?
(define (assumption-proves? hyp j)
  (match* (hyp j)
    [((judgment (has-type t1)) (judgment (has-type t2)))
     (type=? t1 t2)]
    [((judgment is-type) (judgment is-type))
     #t]
    [(_ _)
     #f]))

(define/contract (assumption num)
  (-> natural-number/c rule/c)
  (match-lambda
    [(>> hypotheses goal)
     (if (< num (length hypotheses))
         (match-let ([(hypothesis id hyp _) (list-ref hypotheses num)])
           (if (assumption-proves? hyp goal)
               (done-refining id)
               (refinement-fail
                'assumption
                (>> hypotheses goal)
                (format "Invalid hypothesis: expected ~a, got ~a"
                        (syntax->datum goal)
                        (syntax->datum hyp)))))
         (refinement-fail
          'assumption
          (>> hypotheses goal)
          "Hypothesis out of bounds"))]
    [other (refinement-fail 'assumption
                            other
                            "not a well-formed goal")]))


;;; Rules for building types
(define/contract Int-f rule/c
  (match-lambda
    [(>> _ (judgment is-type))
     (done-refining #'Int)]
    [other (refinement-fail 'Int-f
                            other
                            "wrong goal")]))

(define/contract String-f rule/c
  (match-lambda
    [(>> _ (judgment is-type))
     (done-refining #'String)]
    [other (refinement-fail 'String-f
                            other
                            "wrong goal")]))

(define/contract Fun-f rule/c
  (match-lambda
    [(>> hyps (judgment is-type))
     (proof
      (<- goals (subgoals (>> hyps (judgment is-type))
                          (>> hyps (judgment is-type))))
      (refinement
       goals
       (lambda (dom cod)
         #`(→ #,dom #,cod))))]
    [other (refinement-fail 'String-f
                            other
                            "wrong goal")]))

(define/contract (Forall-f α)
  (-> symbol? rule/c)
  (match-lambda
    [(>> hyps (judgment is-type))
     (proof (let new-scope (make-syntax-introducer))
            (let annotated-name (new-scope (datum->syntax #f α) 'add))
            (<- body (new-meta 'body))
            (pure (refinement (list (subgoal
                                     body
                                     (>> (cons (hypothesis annotated-name
                                                           (judgment is-type)
                                                           #t)
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
    [(>> _ (judgment (has-type (type String))))
     (done-refining (datum->syntax #'here str))]
    [other
     (refinement-fail 'string-intro other "Goal must be String")]))

(define/contract (int-intro i)
  (-> integer? rule/c)
  (match-lambda
    [(>> _ (judgment (has-type (type Int))))
     (done-refining (datum->syntax #'here i))]
    [other
     (refinement-fail 'int-intro other "Goal must be Int")]))


(define/contract (function-intro x)
  (-> symbol? rule/c)
  (match-lambda
    [(>> hyps (judgment (has-type (type (→ τ σ)))))
     (proof (let new-scope (make-syntax-introducer))
            (let annotated-name (new-scope (datum->syntax #f x) 'add))
            (<- body (new-meta 'fun-body))
            (pure (refinement (list (subgoal
                                     body
                                     (>> (cons (hypothesis annotated-name
                                                           (judgment (has-type τ))
                                                           #t)
                                               hyps)
                                         (judgment (has-type σ)))))
                              (lambda (extract)
                                #`(lambda (#,annotated-name)
                                    #,(new-scope extract 'add))))))]
    [other (refinement-fail 'function-intro other "Goal must be function type")]))


(define/contract application rule/c
  (match-lambda
    [(>> hyps (judgment (has-type σ)))
     (displayln σ)
     (proof (<- arg-type (new-meta 'arg-type))
            (<- fun (new-meta 'fun))
            (<- arg (new-meta 'arg))
            (pure
             (refinement
              (list (subgoal arg-type (>> hyps (judgment is-type)))
                    (dependent-subgoal
                     arg-type
                     (lambda (τ) (subgoal fun (>> hyps (judgment (has-type (type (→ τ σ))))))))
                    (dependent-subgoal
                     arg-type
                     (lambda (τ) (subgoal arg (>> hyps (judgment (has-type τ)))))))
              (lambda (t f arg)
                #`(#,f #,arg)))))]))

(define/contract Forall-intro rule/c
  (match-lambda
    [(>> hyps (judgment (has-type (type (∀ α τ)))))
     (proof (<- body (new-meta 'body))
            (pure
             (refinement
              (list (subgoal body (>> (cons (hypothesis α (judgment is-type) #t)
                                            hyps)
                                      (judgment (has-type τ)))))
              identity)))]
    [other (refinement-fail 'forall-intro other "Goal must be universal type")]))
