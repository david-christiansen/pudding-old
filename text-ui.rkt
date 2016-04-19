#lang racket

(require "error-handling.rkt" "infrastructure.rkt")
(provide prover)

;;; UI
(define (display-hypothetical hypothetical)
  (let ([hypotheses (hypothetical-hypotheses hypothetical)]
        [goal (hypothetical-goal hypothetical)])
    (for ([hyp (reverse hypotheses)]
          [which-hyp (range (length hypotheses) 0 -1)])
      (printf "~a. ~a\n" (- which-hyp 1) (syntax->datum (hypothesis-assumption hyp))))
    (printf ">> ~a\n" (syntax->datum goal))))

(define ((display-error header) e)
  (displayln header)
  (parameterize ([current-error-port (current-output-port)])
    ((error-display-handler)
     (exn-message e) e))
  (displayln "Try again!"))

(define (refinement-step path hypothetical relevant? namespace)
  (define (retry) (refinement-step path hypothetical relevant? namespace))
  (if (null? path)
      (display "At top.")
      (begin (display "Position: ")
             (for ([pos (reverse path)])
               (printf "~a " pos))))
  (displayln "")
  (display-hypothetical hypothetical)
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
              (<- (refinement new-goals extractor) (rule hypothetical))
              (let subterms (for/list ([g new-goals]
                                       [pos (range 0 (length new-goals))])
                              (refinement-step (cons pos path)
                                               (subgoal-obligation g)
                                               (subgoal-relevant? g)
                                               namespace)))
              (pure (if relevant?
                        (apply extractor subterms)
                        (void)))))))))

(define (prover goal namespace)
  (let* ([hypothetical (new-goal goal)]
         [result (refinement-step empty hypothetical #t namespace)])
    result))
