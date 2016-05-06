#lang racket

(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt")
(provide prover)

;;; UI
(define (display-sequent sequent)
  (let ([hypotheses (sequent-hypotheses sequent)]
        [goal (sequent-goal sequent)])
    `(>> ,hypotheses ,(syntax->datum goal))))

(define (node-summary prf)
  (match prf
    [(dependent-subgoal _ _) 'dependent]
    [(irrelevant-subgoal g)
     `(_ ,(display-sequent g))]
    [(subgoal n g)
     `(,n ,(display-sequent g))]
    [(complete-proof g _ e _)
     `(complete ,(display-sequent g) ,(syntax->datum e))]
    [(refined-step _ g _ _ _)
     `(refined ,(display-sequent g))]))

(define (show-focus f)
  (match f
    [(dependent-subgoal _ _) 'dependent]
    [(subgoal n g)
     (display-sequent g)]
    [(complete-proof g _ e ch)
     `(complete-proof ,(display-sequent g) ,(syntax->datum e)
                      ,(map node-summary ch))]
    [(refined-step _ g _ ch _)
     `(refined ,(display-sequent g) ,(map node-summary ch))]
    [(? list? xs)
     `(list ,@(map show-focus xs))]
    [(? syntax? stx)
     (syntax->datum stx)]))

(define ((display-error header) e)
  (displayln header)
  (parameterize ([current-error-port (current-output-port)])
    ((error-display-handler)
     (exn-message e) e))
  (displayln "Try again!"))

(define/proof (finish-proof namespace)
  (<- top? at-top?)
  (if (not top?)
      (proof (pure (displayln "Not at top level"))
             (interactive-refiner namespace))
      (proof (<- focus get-focus)
             (if (not (complete-proof? focus))
                 (proof (pure (displayln "Not a complete proof"))
                        (interactive-refiner namespace))
                 (pure (complete-proof-extract focus))))))

(define/proof (interactive-refiner namespace)
  (<- f get-focus)
  (pure (pretty-print (show-focus f)))
  (pure (display "> "))
  (let input (read-syntax))
  (pure (displayln (format "input is ~a" input)))
  (if (eof-object? input)
      (pure #f)
      (match (syntax->datum input)
        [':q (pure #f)]
        [':done (finish-proof namespace)]
        [_ (proof (let tactic (with-handlers ([exn:fail?
                                               proof-pure])
                                (eval input namespace)))
                  (if (exn? tactic)
                      (pure (displayln tactic))
                      tactic)
                  (interactive-refiner namespace))])))

(define (prover goal namespace)
  (proof-eval (interactive-refiner namespace)
              (init-proof-state (new-goal goal))))
