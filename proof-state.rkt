#lang racket

(require zippers
         (rename-in "error-handling.rkt"
                    [proof-get get]
                    [proof-put put]
                    [proof-modify modify])
         "metavariables.rkt"
         "proofs.rkt"
         "infrastructure.rkt")

(provide init-proof-state
         new-meta
         lookup-meta
         instantiated?
         uninstantiated?
         get-focus
         prove
         move
         refine
         solve)

(module+ test
 (require rackunit))

;;; A proof state contains:
;;;
;;;  1. A name supply (here represented as a metavariable context)
;;;  2. A Huet zipper into a proof tree
(struct proof-state
  (metavariables proof))

(define (set-metavariables st new-ctxt)
  (match st
    [(proof-state _ proof) (proof-state new-ctxt proof)]))

(define (init-proof-state goal)
  (let-values ([(ctxt var) (new-metavariable (fresh-context) 'toplevel)])
    (proof-state ctxt (zip (subgoal var goal)))))

(define/proof (new-meta hint)
  (<- st get)
  (let old-ctxt (proof-state-metavariables st))
  (let-values (new-ctxt var) (new-metavariable old-ctxt hint))
  (put (set-metavariables st new-ctxt))
  (pure var))

(define/proof (lookup-meta var)
  (<- (proof-state ctxt _) get)
  (pure (lookup-metavariable ctxt var)))

(module+ test
  (check-equal?
   (proof-eval
    (proof (<- x (new-meta 'x))
           (<- assigned-now (meta-assigned? x))
           (assign-meta x #'"hi there")
           (<- assigned-later (meta-assigned? x))
           (<- val (lookup-meta x))
           (pure (list assigned-now
                       assigned-later
                       (syntax->datum val))))
    (init-proof-state #'whatever))
   '(#f #t "hi there")))

(struct exn:fail:metavariable-already-assigned exn:fail:contract
  (metavariable context)
  #:extra-constructor-name make-exn:fail:metavariable-already-assigned
  #:transparent)

(define/proof (meta-assigned? var)
  (<- (proof-state ctxt _) get)
  (pure (instantiated? (lookup-metavariable ctxt var))))

(define/proof (assign-meta var stx)
  (<- (proof-state ctxt _) get)
  (let val (lookup-metavariable ctxt var))
  (if (instantiated? val)
      (proof-fail (make-exn:fail:metavariable-already-assigned
                   "Metvariable already assigned"
                   (current-continuation-marks)
                   var
                   ctxt))
      (proof (let new-ctxt (assign var stx ctxt))
             (<- st get)
             (put (set-metavariables st new-ctxt)))))

(define/proof get-focus
  (<- (proof-state _ z) get)
  (pure (zipper-focus z)))

(define/proof (edit-focus proc)
  (<- (proof-state ctxt z) get)
  (put (proof-state ctxt (edit proc z))))

(define (set-focus val)
  (edit-focus (thunk* val)))

(define (move . procs)
  (proof
   (<- (proof-state ctxt z) get)
   (put (proof-state ctxt ((apply compose (reverse procs)) z)))))

(struct exn:fail:cant-solve exn:fail:contract ()
  #:extra-constructor-name make-exn:fail:cant-solve
  #:transparent)

(define/proof solve
  (<- (proof-state _ looking-at) get)
  (match (zipper-focus looking-at)
    [(refined-step goal rule children extractor)
     #:when (andmap complete-proof? children)
     (let* ([child-extracts (map complete-proof-extract children)]
            [new-node (complete-proof goal rule (apply extractor child-extracts) children)])
       (set-focus new-node))]
    [(refined-step _ _ children _)
     (proof-fail (make-exn:fail:cant-solve
                  (format "Not all children are complete: ~a"
                          children)
                  (current-continuation-marks)))]
    [other-state
     (proof-fail (make-exn:fail:cant-solve (format "Not a refined proof step: ~a"
                                                   other-state)
                                           (current-continuation-marks)))]))

(struct exn:fail:cant-refine exn:fail:contract
  (looking-at)
  #:extra-constructor-name make-exn:fail:cant-refine
  #:transparent)

(define/proof (refine rule)
  (<- (proof-state ctxt looking-at) get)
  (<- goal (match (zipper-focus looking-at)
             [(subgoal x goal)
              (pure goal)]
             [(irrelevant-subgoal goal)
              (pure goal)]
             [other
              (proof-fail (make-exn:fail:cant-refine
                           "Can't refine"
                           (current-continuation-marks)
                           other))]))
  (<- (refinement new-goals extraction)
      (rule goal))
  (set-focus (refined-step goal rule new-goals extraction)))

(define/proof (make-subgoal hint goal)
  (<- name (new-meta hint))
  (pure (subgoal name goal)))

(module+ test
  (define goal (>> empty #'Int))
  (define (rule-plus n)
    (match-lambda
      [(>> hyps todo)
       #:when (free-identifier=? todo #'Int)
       (proof
        (let names '(a b c d e f g h i j k l m n o p q r s t u v x y z æ ø å))
        (<- subgoals (for/proof/list
                      ([name (in-cycle names)]
                       [i (in-range n)])
                      (make-subgoal name (>> hyps #'Int))))
        (pure (refinement subgoals
                          (lambda args
                            (datum->syntax #'here (cons #'+ args))))))]))
  (define (lit n)
    (match-lambda
      [(>> hyps todo)
       #:when (free-identifier=? todo #'Int)
       (proof (pure (refinement empty (thunk (datum->syntax #'here n)))))]))

  (define (test-a-proof prf)
    (rebuild
     (proof-state-proof
      (proof-eval (proof prf
                         get)
                  (init-proof-state goal)))))
  

  (define proof-1 (test-a-proof (proof (pure (void)))))
  (check-false (complete-proof? proof-1))
  (check-true (subgoal? proof-1))

  (define proof-2 (test-a-proof (refine (lit 1))))
  (check-true (refined-step? proof-2))
  (check-equal? (refined-step-children proof-2) '())

  (define proof-3 (test-a-proof (proof (refine (lit 1))
                                       solve)))
  (check-true (complete-proof? proof-3))
  (check-equal? (syntax->datum (complete-proof-extract proof-3))
                1)

  (check-exn exn:fail:cant-solve?
             (thunk (test-a-proof (proof (refine (rule-plus 3))
                                         solve))))
  (define proof-4 (test-a-proof (proof (refine (rule-plus 3)))))
  (check-true (refined-step? proof-4))
  (check-equal? (length (refined-step-children proof-4)) 3)
  (check-true (andmap subgoal? (refined-step-children proof-4)))

  (define proof-5
    (let ([next-in-list (move up down/cdr down/car)])
      (test-a-proof
       (proof (refine (rule-plus 3))
              (move down/refined-step-children)
              (move down/car)
              (refine (lit -23))
              solve
              next-in-list
              (refine (lit 17))
              solve
              next-in-list
              (refine (lit 42))
              solve
              (move up up up up)
              solve))))
  (check-true (complete-proof? proof-5))
  (check-equal? (syntax->datum (complete-proof-extract proof-5))
                '(+ -23 17 42)))

;; Attempt to prove a goal completely. Return the tree, or throw an
;; exception if incomplete.
(define (prove goal prf)
  (let* ([st (init-proof-state goal)]
         [res (proof-eval (proof prf
                                 (<- (proof-state _ looking-at) get)
                                 (pure (rebuild looking-at)))
                          st)])
    (if (complete-proof? res)
        res
        (raise (make-exn:fail (format "Incomplete proof: ~a" res) (current-continuation-marks))))))
