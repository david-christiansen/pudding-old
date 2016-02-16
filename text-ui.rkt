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
    ((error-display-handler) (exn-message e) e))
  (displayln "Try again!"))

(define/contract (refinement-step path sequent namespace)
  (-> (listof exact-nonnegative-integer?) sequent? namespace? syntax?)
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
    (with-fallbacks ([refinement-error? (lambda (e)
                                          ((display-error "Refinement failed:") e)
                                          (retry))])
      (let* ([input (read)])
        (if (equal? input ':q)
            (begin (printf "Exiting, proof incomplete\n") (exit 0))
            (let ([rule (eval input namespace)])
              (match! (rule sequent)
                [(refinement new-goals extractor)
                 (let ([subterms (for/list ([g new-goals]
                                            [pos
                                             (range 0
                                                    (length new-goals))])
                                   (refinement-step (cons pos path)
                                                    g
                                                    namespace))])
                   (success (apply extractor subterms)))])))))))


(define (prover goal namespace)
  (let* ([sequent (new-goal goal)]
         [result (refinement-step empty sequent namespace)])
    result))
