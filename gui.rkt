#lang racket

(require racket/gui)

(require zippers)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt")

(define goal-view-panel%
  (class vertical-panel%
    (init-field goal)
    (init parent)
    (super-new [parent parent])

    (define/public (update)
      (match goal
        [(>> hyps todo)
         (for ([h hyps]
               [i (range (length hyps) 0 -1)])
           (match-define (hypothesis name assumption relevant?) h)
           (define row (new horizontal-panel% [parent this]))
           (new button%
                [parent row]
                [label (format "~a: ~a" i name)]
                [enable relevant?]
                [callback (thunk* (void))])
           (new message%
                [parent row]
                [label (format "~a" (syntax->datum assumption))])
           (void))
         (new message%
              [parent this]
              [label (format "~a" (syntax->datum todo))])]))

    (send this update)))



(define prover-frame%
  (class frame%
    (init-field proof-state)
    (init rule-namespace
          [width 800]
          [height 600])
    (super-new [label "Proof editor"] [width width] [height height])

    ;; Apply an action in the proof monad
    (define/public (run-action act)
      (let-values ([(res new-state) (proof-run act proof-state)])
        (set-field! proof-state this new-state)
        (update-movement-buttons)
        res))

    (define (refine-with rule)
      (run-action (refine rule)))

    (define stack (new vertical-panel% [parent this]))

    (define navbar (new horizontal-panel% [parent stack]))

    (define movement-buttons '())

    (define (make-movement-button label direction)
      (let ([the-button
             (new button%
                  [parent navbar]
                  [label label]
                  [callback (lambda (button event)
                              (run-action (move direction)))])])
        (set! movement-buttons (cons (cons the-button direction)
                                     movement-buttons))
        the-button))

    (define (update-movement-buttons)
      (for ([button+dir movement-buttons])
        (define button (car button+dir))
        (define dir (cdr button+dir))
        (send button enable (run-action (movement-possible? dir)))))

    (define up-button
      (make-movement-button "Up" up))
    (define left-button
      (make-movement-button "Left" left/list))
    (define right-button
      (make-movement-button "Right" right/list))

    (update-movement-buttons)


    (define goal-viewer
      (new goal-view-panel%
           [parent stack]
           [goal (proof-step-goal (send this run-action get-focus))]))

    (define rule-input
      (new text-field%
           [parent stack]
           [label "Refinement rule"]
           [callback
            (lambda (field evt)
              (when (eqv? (send evt get-event-type) 'text-field-enter)
                (with-handlers ([exn:fail? displayln]) ;; todo error display
                  (refine-with
                   (eval-syntax
                    (with-input-from-string (send field get-value)
                      read-syntax)
                    rule-namespace)))))]))))

(define (prover namespace goal)
  (define frame (new prover-frame%
                     [proof-state (init-proof-state (new-goal goal))]
                     [rule-namespace namespace]))
  (send frame show #t)
  (void))


(module stlc-prover-context racket/base
  (require "theories/stlc.rkt")
  (require "tactics.rkt")
  (require zippers)
  (require "proof-state.rkt")
  (require "proofs.rkt")

  (provide stlc-anchor)

  (define-namespace-anchor stlc-anchor))

(require
 'stlc-prover-context)

(define (test-prover)
  (prover (namespace-anchor->namespace stlc-anchor) #'(--> String Int)))
