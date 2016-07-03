#lang racket

(require (for-syntax racket/syntax syntax/parse)
         syntax/parse
         zippers
         "infrastructure.rkt"
         "error-handling.rkt"
         "proof-state.rkt"
         "proofs.rkt")
(provide rule define-rule)

(module+ test (require rackunit))


(begin-for-syntax
  (define-syntax-class underscore
    #:literals (_)
    #:description "underscore"
    (pattern _))

  (define-syntax-class sequent-stx
    #:literals (>>)
    #:description "sequent"
    (pattern (>> hypotheses:expr goal:expr)))

  (define-syntax-class subgoal
    #:attributes (name depends-on hypotheses conclusion)
    ;; Irrelevant goals
    (pattern (u:underscore goal:sequent-stx)
             #:attr depends-on '()
             #:attr name #f
             #:attr hypotheses (attribute goal.hypotheses)
             #:attr conclusion (attribute goal.goal))
    ;; Irrelevant dependent goals
    (pattern (u:underscore (deps:id ...+) goal:sequent-stx)
             #:attr name #f
             #:attr depends-on (syntax->list #'(deps ...))
             #:attr hypotheses (attribute goal.hypotheses)
             #:attr conclusion (attribute goal.goal))
    ;; Dependent goals
    (pattern (name:id (deps:id ...+) goal:sequent-stx)
             #:attr depends-on (syntax->list #'(deps ...))
             #:attr hypotheses (attribute goal.hypotheses)
             #:attr conclusion (attribute goal.goal))
    ;; Normal goals
    (pattern (name:id goal:sequent-stx)
             #:attr depends-on '()
             #:attr hypotheses (attribute goal.hypotheses)
             #:attr conclusion (attribute goal.goal))))

(define-syntax (only-underscore stx)
  (syntax-parse stx
    [(any x:underscore) #'#t]
    [(any other) #'#f]))

(define-for-syntax (make-dependent orig-stx metavars name deps hyps concl)
  (cond
    [(pair? deps)
     (let ([metavar-name (assoc (car deps)
                                metavars
                                free-identifier=?)])
       (if metavar-name
           (quasisyntax/loc orig-stx
             (dependent-subgoal
              #,(cdr metavar-name)
              (lambda (#,(cdr metavar-name))
                (with-syntax ([#,(car deps) #,(cdr metavar-name)])
                  #,(make-dependent orig-stx
                                    metavars
                                    name
                                    (cdr deps)
                                    hyps
                                    concl)))))
           (raise-syntax-error
            'rule "Unknown subgoal name" (car deps))))]
    [name
     (let ([metavar-name (assoc name
                                metavars
                                free-identifier=?)])
       (if metavar-name
           (with-syntax ([mv-name (cdr metavar-name)]
                         [hs hyps]
                         [goal concl])
             (syntax/loc orig-stx
               (subgoal mv-name (>> hs #`goal))))
           (raise-syntax-error
            'rule "Internal error: No metavariable" orig-stx)))]
    [else
     (quasisyntax/loc orig-stx
       (irrelevant-subgoal (>> #,hyps (syntax #,concl))))]))

(define-for-syntax ((rule-clause msg lits dat-lits lit-sets) stx)
  (syntax-parse stx
    [(lhs:sequent-stx (subgoals:subgoal ...) extract:expr)
     (let ([names (attribute subgoals.name)]
           [hyps (attribute subgoals.hypotheses)]
           [concls (attribute subgoals.conclusion)]
           [deps (attribute subgoals.depends-on)])
       (let ([metavars
              (for/list ([n names] #:when n)
                (cons n (format-id stx "~a-metavar" n #:source n)))]
             [extract-vars
              (for/list ([n names] #:when n)
                (cons n (format-id stx "~a-ext" n #:source n)))])
         (with-syntax* ([failure-message msg]
                        [literals lits]
                        [datum-literals dat-lits]
                        [literal-sets lit-sets]
                        [(metavar-decls ...)
                         (for/list ([meta metavars])
                           #`(<- #,(cdr meta) (new-meta '#,(car meta))))]
                        [(new-goals ...)
                         (for/list ([n names]
                                    [d deps]
                                    [h hyps]
                                    [c concls])
                           (make-dependent stx metavars n d h c))]
                        [(extract-binding ...) (map cdr extract-vars)]
                        [(extract-stx-binding ...)
                         (for/list ([e extract-vars])
                           #`(#,(car e) #,(cdr e)))])
           #'[(>> lhs.hypotheses some-goal)
              (syntax-parse some-goal
                #:literals literals
                #:datum-literals datum-literals
                #:literal-sets literal-sets
                [lhs.goal
                 (proof
                  metavar-decls ...
                  (let goals (list new-goals ...))
                  (pure (refinement goals
                                    (lambda (extract-binding ...)
                                      (with-syntax (extract-stx-binding ...)
                                        (quasisyntax extract))))))]
                [_  (proof-fail (make-exn:fail failure-message (current-continuation-marks)))])])))]))


(define-syntax (rule stx)
  (syntax-parse stx
    [(_ (~or (~optional (~seq #:literals literals:expr)
                        #:defaults ([literals #'()])
                        #:name "literals")
             (~optional (~seq #:datum-literals datum-literals:expr)
                        #:defaults ([datum-literals #'()])
                        #:name "datum literals")
             (~optional (~seq #:datum-literals literal-sets:expr)
                        #:defaults ([literal-sets #'()])
                        #:name "literal sets")
             (~optional (~seq #:failure-message failure-message:str)
                        #:defaults ([failure-message #'"Can't refine"])
                        #:name "failure message")
             (~optional (~seq #:scopes (scopes:id ...))
                        #:defaults ([(scopes 1) null])
                        #:name "scope names"))
        ...
        alt
        ...)
     (with-syntax ([(alternatives ...)
                    (map (rule-clause (attribute failure-message)
                                      (attribute literals)
                                      (attribute datum-literals)
                                      (attribute literal-sets))
                         (attribute alt))]
                   [(scope-bindings ...)
                    (map (lambda (scope-name)
                           (quasisyntax/loc scope-name
                             [#,scope-name (make-syntax-introducer)]))
                         (syntax->list #'(scopes ...)))])
       #`(lambda (st)
           (let (scope-bindings ...)
             (match st
               alternatives ...
               [other (proof-fail (make-exn:fail:cant-refine failure-message
                                                             (current-continuation-marks)
                                                             other))]))))]))

(define-syntax (define-rule stx)
  (syntax-parse stx
    [(_ n:id defn ...)
     #'(define n
         (rule defn ...))]
    [(_ (n:id args ...) defn ...)
     #'(define (n args ...)
         (rule defn ...))]))

(module+ test
  ;;; This macro relies on with-syntax bound syntax pattern variables
  ;;; to have lexical scope. Ensure that this is the case!
  (check-eqv? (syntax->datum
               (let ([f (with-syntax ([a #'fnord]) (lambda (x) #'a))])
                 (f 3)))
              'fnord)

  ;;; Bindings for this type theory
  (define-syntax (Σ stx)
    (raise-syntax-error 'Σ "Type used out of context" stx))
  (define-syntax (Π stx)
    (raise-syntax-error 'Π "Type used out of context" stx))
  (define-syntax (Bool stx)
    (raise-syntax-error 'Bool "Type used out of context" stx))
  (define-syntax (So stx)
    (raise-syntax-error 'So "Type used out of context" stx))
  (define-syntax (Type stx)
    (raise-syntax-error 'Type "Type used out of context" stx))

  ;; TODO: check that bound-identifier=? is what we want to avoid
  ;; capture
  (define (subst new-stx x in)
    (syntax-parse in
      #:literals (Σ Π Bool So cons lambda)
      [(Σ (y:id A) B)
       #`(Σ (y #,(subst new-stx x #'A))
            (if (bound-identifier=? #'y x)
                #,(subst new-stx x #'B)
                #'B))]
      [(Π (y:id A) B)
       #`(Π (y #,(subst new-stx x #'A))
            (if (bound-identifier=? #'y x)
                #,(subst new-stx x #'B)
                #'B))]
      [(lambda (y:id) B)
       #`(lambda (y)
           (if (bound-identifier=? #'y x)
               #,(subst new-stx x #'B)
               #'B))]
      [Bool #'Bool]
      [(So body)
       #`(So #,(subst new-stx x #'body))]
      [y:id
       #:when (bound-identifier=? #'y x)
       new-stx]
      [(cons e1 e2)
       #`(cons #,(subst new-stx x #'e1)
               #,(subst new-stx x #'e2))]
      [(e:expr ...)
       (datum->syntax in (map (lambda (e)
                                (subst new-stx x e))
                              (syntax->list #'(e ...))))]
      [other
       #'other]))

  (define-rule (Σ-formation x)
    #:literals (Σ)
    #:scopes (new-scope)
    [(>> H Type)
     ([A (>> H Type)]
      [B (A) (>> (cons (hypothesis (new-scope (datum->syntax #f x) 'add)
                                   #'A
                                   #t)
                       H)
                 Type)])
     (Σ (#,(new-scope (datum->syntax #f x) 'add)
         A)
        #,(new-scope #'B 'add))])

  (define-rule Σ-intro
    #:literals (Σ)
    [(>> H (Σ (x:id A) B))
     ([a (>> H A)]
      [b (a) (>> H #,(subst #'a #'x #'B))])
     (cons a b)])

  (define-rule Bool-formation
    #:literals (Type)
    [(>> H Type)
     ()
     Bool])

  (define-rule Bool-intro-1
    #:literals (Bool)
    [(>> H Bool)
     ()
     #t])

  (define-rule Bool-intro-2
    #:literals (Bool)
    [(>> H Bool)
     ()
     #f])

  (define-rule So-intro
    #:literals (So quote)
    #:failure-message "Can only be used with #t"
    [(>> H (So #t))
     ()
     (void)])

  (define prf-1
    (proof-eval (proof (refine Σ-intro)
                       (move (down/proof))
                       (refine Bool-intro-1)
                       solve
                       (move right/proof)
                       dependent
                       (refine So-intro)
                       solve
                       (move up)
                       solve
                       get-focus)
                (init-proof-state (>> null #'(Σ (y Bool) (So y))))))
  (check-equal? (syntax->datum (complete-proof-extract prf-1))
                '(cons #t (void)))

  (define prf-2
    (thunk (proof-eval (proof (refine Σ-intro)
                              (move (down/proof))
                              (refine Bool-intro-2)
                              solve
                              (move right/proof)
                              dependent
                              (refine So-intro)
                              solve
                              (move up)
                              solve
                              get-focus)
                       (init-proof-state (>> null #'(Σ (y Bool) (So y)))))))
  (check-exn exn:fail? prf-2)

  (define Bool-pair-type
    (complete-proof-extract
     (proof-eval (proof (refine (Σ-formation 't))
                        (move (down/proof))
                        (refine Bool-formation)
                        solve
                        (move right/proof)
                        dependent
                        (refine Bool-formation)
                        solve
                        (move up)
                        solve
                        get-focus)
                 (init-proof-state (>> null #'Type)))))

  (define pair-of-bools
    (complete-proof-extract
     (proof-eval (proof (refine Σ-intro)
                        (move (down/proof))
                        (refine Bool-intro-1)
                        solve
                        (move right/proof)
                        dependent
                        (refine Bool-intro-2)
                        solve
                        (move up)
                        solve
                        get-focus)
                 (init-proof-state (>> null Bool-pair-type)))))
  #;
  (check-equal? (syntax->datum pair-of-bools)
                '(cons #t #f)))

