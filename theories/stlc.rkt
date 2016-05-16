#lang racket

(require syntax/parse (for-syntax syntax/parse))
#;(require macro-debugger/syntax-browser)
(require "../error-handling.rkt" "../define-rule.rkt" "../infrastructure.rkt"
         "../proofs.rkt" "../proof-state.rkt")

(require (for-template racket/base racket/match))

(provide stlc
         type? --> Int String
         addition application function-intro assumption int-intro
         length-of-string string-intro )

(define-namespace-anchor stlc)

;; These definitions aren't really used for anything. They're here to
;; get a top-level binding for use in syntax objects representing
;; types.
(define-syntax (Int stx)
  (raise-syntax-error #f "Type used out of context"))
(define-syntax (String stx)
  (raise-syntax-error #f "Type used out of context"))
(define-syntax (--> stx)
  (raise-syntax-error #f "Type used out of context"))

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
(define/contract (assumption num)
  (-> natural-number/c rule/c)
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
                                      (current-continuation-marks)))]))


;;; Int rules
(define/contract (int-intro x)
  (-> integer? rule/c)
  (with-syntax ([x x])
    (rule #:failure-message "Goal type must be Int"
          #:datum-literals (Int)
          [(>> _ Int)
           ()
           x])))

(define/contract (addition arg-count)
  (-> natural-number/c rule/c)
  (lambda (goal)
    (match goal
      [(>> hypotheses (type Int))
       (proof
        (<- subgoals (for/proof/list
                      ([n (in-cycle '(a b c d e f g h i j k l m n))]
                       [i (in-range arg-count)])
                      (<- v (new-meta n))
                      (pure (subgoal v (>> hypotheses (type Int))))))
        (pure (refinement subgoals
                          (lambda arguments
                            (datum->syntax #'here (cons #'+ arguments))))))]
      [other (proof-fail (make-exn:fail "goal type must be Int"
                                        (current-continuation-marks)))])))

(define/contract length-of-string rule/c
  (rule
   #:failure-message  "Goal type must be Int"
   [(>> hypotheses Int)
    ([a-string (>> hypotheses String)])
    (string-length a-string)]))

;;; String rules
(define/contract (string-intro str)
  (-> string? rule/c)
  (with-syntax ([str str])
   (rule #:failure-message  "Goal type must be String"
         #:datum-literals (String)
         [(>> _ String)
          ()
          str])))

;;; Function rules
(define/contract (function-intro x)
  (-> symbol? rule/c)
  (with-syntax ([x x])
    (rule #:failure-message "Goal must be function type"
          #:datum-literals (-->)
          #:scopes (new-scope)
          [(>> hyps (--> dom cod))
           ([body (>> (cons (hypothesis (new-scope #'x 'add)
                                        #'dom
                                        #t)
                            hyps)
                      cod)])
           (lambda (#,(new-scope #'x 'add))
             #,(new-scope #'body 'add))])))

;; TODO - rewrite using dependent refinement
(define/contract ((application dom) proof-goal)
  (-> syntax? rule/c)
  (unless (type? dom)
    (proof-fail (make-exn:fail (format "Not a type: ~a" dom)
                               (current-continuation-marks))))
  (match proof-goal
    [(>> hypotheses goal)
     (proof
      (<- f (new-meta 'fun))
      (<- x (new-meta 'arg))
      (pure
       (refinement
        (list (subgoal f (>> hypotheses #`(--> #,dom #,goal)))
              (subgoal x (>> hypotheses dom)))
        (lambda (fun arg)
          #`(#,fun #,arg)))))]))

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


