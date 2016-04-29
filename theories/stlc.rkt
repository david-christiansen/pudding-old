#lang racket

(require syntax/parse (for-syntax syntax/parse))
#;(require macro-debugger/syntax-browser)
(require "../error-handling.rkt" "../infrastructure.rkt" "../proofs.rkt"
         "../proof-state.rkt")

(require (for-template racket/base racket/match))

(provide stlc
         type? --> Int String
         addition application function-intro assumption int-intro
         length-of-string string-intro )

(define-namespace-anchor stlc)

;; These definitions aren't really used for anything. They're here to
;; get a top-level binding for use in syntax objects representing
;; types.
(define-syntax (Int stx) (raise-syntax-error #f "Type used out of context"))
(define-syntax (String stx) (raise-syntax-error #f "Type used out of context"))
(define-syntax (--> stx) (raise-syntax-error #f "Type used out of context"))

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
  (match-lambda
    [(>> _ (type Int))
     (done-refining (datum->syntax #'here x))]
    [other (proof-fail (make-exn:fail "goal type must be Int"
                                      (current-continuation-marks)))]))

(define/contract (addition arg-count)
  (-> natural-number/c rule/c)
  (lambda (hypothetical)
    (match hypothetical
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

(define/contract (length-of-string hypothetical) rule/c
  (match hypothetical
    [(>> hypotheses (type Int))
     (proof
      (<- x (new-meta 'a-string))
      (pure (refinement
             (list (subgoal x (>> hypotheses (type String))))
             (lambda (argument)
               #`(string-length #,argument)))))]
    [other
     (proof-fail (make-exn:fail "Goal type must be Int" (current-continuation-marks)))]))

;;; String rules
(define/contract (string-intro str)
  (-> string? rule/c)
  (match-lambda
    [(>> _ (type String))
     (done-refining (datum->syntax #'here str))]
    [other (proof-fail (make-exn:fail "Goal type must be String"
                                      (current-continuation-marks)))]))

;;; Function rules
(define/contract (function-intro x)
  (-> symbol? rule/c)
  (match-lambda
    [(>> hyps (type (--> dom cod)))
     (proof (let new-scope (make-syntax-introducer))
            (let annotated-name (new-scope (datum->syntax #f x) 'add))
            (<- name (new-meta 'body))
            (pure (refinement
                   (list (subgoal
                          name
                          (>> (cons (hypothesis annotated-name
                                                dom
                                                #t)
                                    hyps)
                              cod)))
                   (lambda (extract)
                     #`(lambda (#,annotated-name)
                         #,(new-scope extract 'add))))))]
    [other (proof-fail (make-exn:fail "Goal must be function type"
                                      (current-continuation-marks)))]))

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


