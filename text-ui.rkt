#lang racket

(require "infrastructure.rkt")
(provide prover)

;;; UI
(define (display-sequent sequent)
  (let ([hypotheses (sequent-hypotheses sequent)]
        [goal (sequent-goal sequent)])
    (for ([hyp (reverse hypotheses)]
          [which-hyp (range (length hypotheses) 0 -1)])
      (printf "~a. ~a\n" (- which-hyp 1) (syntax->datum (cdr hyp))))
    (printf ">> ~a\n" (syntax->datum goal))))

(define (refinement-step path sequent namespace)
  (if (null? path)
      (display "At top.")
      (begin (display "Position: ")
             (for ([pos (reverse path)])
               (printf "~a " pos))))
  (displayln "")
  (display-sequent sequent)
  (display "> ")
  (with-handlers ([exn:fail? (lambda (e)
                               (displayln "Refinement error:")
                               (parameterize ([current-error-port (current-output-port)])
                                 ((error-display-handler) (exn-message e) e))
                               (displayln "Try again!")
                               (refinement-step path sequent namespace))])
    (let* ([rule (eval (read) namespace)]
           [next (rule sequent)])
      (match next
        [(refinement new-goals extractor)
         (let ([subterms (for/list ([g new-goals]
                                    [pos (range 0 (length new-goals))])
                           (refinement-step (cons pos path) g namespace))])
           (apply extractor subterms))]))))


(define (prover goal namespace)
  (let* ([sequent (new-goal goal)]
         [result (refinement-step empty sequent namespace)])
    result))
