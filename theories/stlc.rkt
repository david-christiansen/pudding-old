#lang racket

(require syntax/parse (for-syntax syntax/parse))
#;(require macro-debugger/syntax-browser)
(require "../error-handling.rkt" "../define-rule.rkt" "../infrastructure.rkt"
         "../proofs.rkt" "../proof-state.rkt" "../standard-resources.rkt")

(require (for-template racket/base racket/match))

(provide stlc
         type? --> Int String
         addition application function-intro assumption int-intro
         length-of-string string-intro )

(define-namespace-anchor stlc)

(struct Int ())
(struct String ())
(struct --> (dom cod))
;; (define-syntax (Int stx)
;;   (raise-syntax-error #f "Type used out of context"))
;; (define-syntax (String stx)
;;   (raise-syntax-error #f "Type used out of context"))
;; (define-syntax (--> stx)
;;   (raise-syntax-error #f "Type used out of context"))

(define-match-expander type
  (lambda (stx)
    (syntax-parse stx
      #:literals (-->)
      [(type (--> t1 t2))
       #'(app syntax->list (list _ t1 t2))]
      [(type Int)
       #'(? (lambda (stx) (and (identifier? stx)
                               (free-identifier=? stx #'Int))))]
      [(type String)
       #'(? (lambda (stx) (and (identifier? stx)
                               (free-identifier=? stx #'String))))]))
  (lambda (stx)
    (syntax-parse stx
      #:literals (-->)
      [(type (--> t1 t2))
       #'(syntax (--> t1 t2))]
      [(type Int)
       #'(syntax Int)]
      [(type String)
       #'(syntax String)])))

(define (type? stx)
  (match stx
    [(type (--> t1 t2))
     (and (type? t1)
          (type? t2))]
    [(type Int) #t]
    [(type String) #t]
    [_ #f]))

(define (type=? left right)
  (match* (left right)
    [((type (--> t1 t2))
      (type (--> s1 s2)))
     (and (type=? t1 s1)
          (type=? t2 s2))]
    [((type Int) (type Int))
     #t]
    [((type String) (type String))
     #t]
    [(_ _) #f]))

;;; Structural rules
(define/contract assumption
  rule/c
  (refinement-rule
   'assumption
   (list (rule-parameter 'num 'hypothesis))
   (lambda (num)
     (match-lambda
       [(>> hypotheses goal)
        (if (< num (length hypotheses))
            (match-let ([(hypothesis id type visible?) (list-ref hypotheses num)])
              (cond
                [(not visible?)
                 (proof-fail (make-exn:fail "Tried to use an irrelevant hypothesis"
                                            (current-continuation-marks)))]
                [(type=? type goal)
                 (done-refining id)]
                [else (proof-fail
                       (make-exn:fail (format "Type mismatch: expected ~a, got ~a"
                                              (syntax->datum goal)
                                              (syntax->datum type))
                                      (current-continuation-marks)))]))
            (proof-fail
             (make-exn:fail "Assumption out of bounds"
                            (current-continuation-marks))))]
       [other (proof-fail (make-exn:fail "not a well-formed goal"
                                         (current-continuation-marks)))]))))


;;; Int rules
(define-rule (int-intro [x term])
  #:failure-message "Goal type must be Int"
  #:datum-literals (Int)
  #:pre (integer? (syntax-e x))
  [(>> _ Int)
   ()
   #,x])

(define addition
  (refinement-rule
   'addition
   (list (rule-parameter 'arg-count 'count))
   (lambda (arg-count)
     (match-lambda
       [(>> hypotheses (type Int))
        (proof
         (<- subgoals (for/proof/list
                          ([n (in-cycle '(a b c d e f g h i j k l m n))]
                           [i (in-range arg-count)])
                        (<- v (new-meta n))
                        (pure (subgoal v (>> hypotheses (type Int))))))
         (pure (refinement subgoals
                           (lambda arguments
                             (datum->syntax #'here (cons #'+ arguments))))))]))))

(define-rule length-of-string
  #:failure-message  "Goal type must be Int"
  [(>> hypotheses Int)
   ([a-string (>> hypotheses String)])
   (string-length a-string)])

;;; String rules
(define-rule (string-intro [str term])
  #:pre (string? (syntax->datum str))
  #:failure-message  "Goal type must be String"
  #:datum-literals (String)
  [(>> _ String)
   ()
   #,str])

;;; Function rules
(define-rule (function-intro [x name])
  #:failure-message "Goal must be function type"
  #:datum-literals (-->)
  #:scopes (new-scope)
  [(>> hyps (--> dom cod))
   ([body (>> (cons (hypothesis (new-scope (datum->syntax #f x) 'add)
                                #'dom
                                #t)
                    hyps)
              cod)])
   (lambda (#,(new-scope (datum->syntax #f x) 'add))
     body)])

;; TODO - rewrite using dependent refinement
(define-rule (application [dom term])
  #:pre (type? dom)
  [(>> hypotheses goal)
   ([fun (>> hypotheses (--> #,dom goal))]
    [arg (>> hypotheses #,dom)])
   (fun arg)])

;;; Operational semantics
(define (run-program stx [env empty])
  (syntax-parse stx
    #:literals (lambda + string-length)
    [x
     #:when (identifier? #'x)
     (let ([v (assoc #'x env bound-identifier=?)])
       (if v
           (cdr v)
           (error (format "Variable not found: ~a" #'x))))]
    [x
     #:when (number? (syntax-e #'x))
     #'x]
    [x
     #:when (string? (syntax-e #'x))
     #'x]
    [(lambda (x:id) body)
     stx]
    [(string-length arg)
     (datum->syntax #'here (string-length (syntax-e (run-program #'arg env))))]
    [(+ arg ...)
     (apply + (map (compose syntax->datum
                            (lambda (x) (run-program x env)))
                   (syntax-e #'(arg ...))))]
    [(e1 e2)
     (let ([e1-value (run-program #'e1)]
           [e2-value (run-program #'e2)])
       (syntax-parse e1-value
         [(lambda (x:id) body)
          (run-program #'body (cons (cons #'x e2-value) env))]
         [_ (error (format "Not a function: ~a" e1-value))]))]))


;;; Useful tactics
(define/proof intro
  (<- focus get-focus)
  (match focus
    [(subgoal _ (>> H goal))
     (syntax-parse goal
       #:datum-literals (-->)
       [(--> dom cod)
        (refine (function-intro 'x))])]
    [_ (proof-error "Cannot introduce." )]))

(intro-tactics intro)
