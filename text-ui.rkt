#lang racket

(require "error-handling.rkt" "infrastructure.rkt")
(provide prover)

;;; UI
(define (display-sequent sequent)
  (let ([hypotheses (sequent-hypotheses sequent)]
        [goal (sequent-goal sequent)])
    (for ([hyp (reverse hypotheses)]
          [which-hyp (range (length hypotheses) 0 -1)])
      (printf "~a. ~a\n" (- which-hyp 1) (syntax->datum (cdr hyp))))
    (printf ">> ~a\n" (syntax->datum goal))))

(define ((display-error header) e)
  (displayln header)
  (parameterize ([current-error-port (current-output-port)])
    ((error-display-handler)
     (exn-message e) e))
  (displayln "Try again!"))

(define (refinement-step path sequent namespace)
  (define (retry) (refinement-step path sequent namespace))
  (if (null? path)
      (display "At top.")
      (begin (display "Position: ")
             (for ([pos (reverse path)])
               (printf "~a " pos))))
  (displayln "")
  (display-sequent sequent)
  (display "> ")
  (with-handlers ([exn:fail? (lambda (e)
                               ((display-error "Exception during refinement:") e)
                               (retry))])
    (with-fallbacks refinement-error
      ([refinement-error? (lambda (e)
                            ((display-error "Refinement failed:")
                             (exn:fail (refinement-error-message e)
                                       (current-continuation-marks)))
                            (retry))])
      (let* ([input (read)])
        (if (equal? input ':q)
            (begin (printf "Exiting, proof incomplete\n") (exit 0))
            (error-do refinement-error
              (let rule (call-with-values
                         (thunk (eval input namespace))
                         (lambda args
                           (if (cons? args)
                               (car args)
                               (error 'refinement-step "Didn't get a rule")))))
              (<- (refinement new-goals extractor) (rule sequent))
              (let subterms (for/list ([g new-goals]
                                       [pos (range 0 (length new-goals))])
                                (refinement-step (cons pos path)
                                                 g
                                                 namespace)))
              (pure (apply extractor subterms))))))))

(define (prover goal namespace)
  (let* ([sequent (new-goal goal)]
         [result (refinement-step empty sequent namespace)])
    result))
