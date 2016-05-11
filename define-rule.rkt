#lang racket

(require (for-syntax racket/syntax syntax/parse)
         syntax/parse
         zippers
         "infrastructure.rkt"
         "error-handling.rkt"
         "proof-state.rkt"
         "proofs.rkt")
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
                        #:defaults ([failure-message #'"Can't refine"])))
        ...
        alt
        ...)
     (with-syntax ([(alternatives ...)
                    (map (rule-clause (attribute failure-message)
                                      (attribute literals)
                                      (attribute datum-literals)
                                      (attribute literal-sets))
                         (attribute alt))])
       #`(match-lambda
           alternatives ...
           [other (proof-fail (make-exn:fail failure-message
                                             (current-continuation-marks)))]))]))

(define-syntax (define-rule stx)
  (syntax-parse stx
    [(_ n:id defn ...)
     #'(define n
         (rule defn ...))]
    [(_ (n:id args ...) defn ...)
     #'(define (n args ...)
         (rule defn ...))]))

(module+ test
  (define Σ #f)
  (define Q #f)
  (define qp #f)


  ;; TODO: non-naive substitution (but this is OK for testing define-rule)
  (define (subst new-stx x in)
    (syntax-parse in
      #:literals (Σ Q qp)
      [(Σ (y:id A) B)
       #`(Σ (y #,(subst new-stx x #'A))
            (if (free-identifier=? #'y x)
                #,(subst new-stx x #'B)
                #'B))]
      [Q #'Q]
      [(qp body)
       #`(qp #,(subst new-stx x #'body))]
      [y:id
       #:when (free-identifier=? #'y x)
       new-stx]
      [(e:expr ...)
       (datum->syntax in (map (lambda (e)
                                (subst new-stx x e))
                              (syntax->list #'(e ...))))]
      [other
       #'other]))

  (define-rule Σ-intro
    #:literals (Σ)
    [(>> H (Σ (x A) B))
     ([a (>> H A)]
      [b (a) (>> H #,(subst #'a #'x #'B))])
     (cons a b)])

  (define-rule Q-intro-1
    #:literals (Q)
    [(>> H Q)
     ()
     'q])

  (define-rule Q-intro-2
    #:literals (Q)
    [(>> H Q)
     ()
     'other-q])

  (define-rule qp-intro
    #:literals (qp quote)
    #:datum-literals (q)
    #:failure-message "Can only be used with q"
    [(>> H (qp 'q))
     ()
     'yep-q])

  (define prf-1
    (proof-eval (proof (refine Σ-intro)
                       (move down/refined-step-children down/list-first)
                       (refine Q-intro-1)
                       solve
                       (move right/list)
                       (refine qp-intro)
                       solve
                       (move up up)
                       solve
                       get-focus)
                (init-proof-state (>> null #'(Σ (y Q) (qp y))))))
  (check-equal? (syntax->datum (complete-proof-extract prf-1))
                '(cons 'q 'yep-q))
  (define prf-2
    (thunk (proof-eval (proof (refine Σ-intro)
                              (move down/refined-step-children down/list-first)
                              (refine Q-intro-2)
                              solve
                              (move right/list)
                              (refine qp-intro)
                              solve
                              (move up up)
                              solve
                              get-focus)
                       (init-proof-state (>> null #'(Σ (y Q) (qp y)))))))
  (check-exn exn:fail? prf-2))
