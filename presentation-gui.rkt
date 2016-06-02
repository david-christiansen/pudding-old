#lang racket

(require racket/gui framework presentations pict)
(require zippers)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt")

(define (read-with-length-from str)
  (define port (open-input-string str))
  (define output (read port))
  (values output (file-position port)))

(define proof-script-text%
  (class text%
    (init-field advance-callback retract-callback error-callback)
    (super-new)

    (inherit change-style
             get-text)

    (send this set-styles-sticky #f)

    ;;; Style for accepted region and editable region
    (define accepted-bg
      (send (make-object style-delta%) set-delta-background
            "green"))

    (define editable-bg
      (send (make-object style-delta%) set-delta-background
            "white"))

    ;;; The editor positions that constitute the ends of each accepted
    ;;; proof step. When advancing the accepted region, the new
    ;;; position is consed on to this.
    (define steps
      '(0))
    (define (save-step! pos)
      (set! steps (cons pos steps)))

    (define (update-bg)
      (change-style accepted-bg 0 (car steps) #f)
      (change-style editable-bg (car steps) 'end #f))

    (define/augment (can-insert? start len)
      (>= start (car steps)))

    (define/augment (can-delete? start len)
      (>= start (car steps)))

    ;;; Run a command
    (define/public (advance)
      (with-handlers ([exn? error-callback])
        (define step (car steps))
        (define text (get-text step))
        (define-values (val len) (read-with-length-from text))
        (save-step! (+ step len))
        (queue-callback (thunk (update-bg)))
        (queue-callback (thunk (advance-callback val)))))

    (define/public (retract)
      (when (and (pair? steps) (pair? (cdr steps)))
        (set! steps (cdr steps))
        (queue-callback (thunk (update-bg)))
        (queue-callback (thunk (retract-callback)))))))

(define (present-term tm)
  (define tm-pict (inset (text (format "~v" (syntax->datum tm))) 8))
  (new presentation-img%
       [object tm]
       [modality '(term)]
       [img (new pict-img%
                 [pict (cc-superimpose
                        (filled-rectangle (pict-width tm-pict)
                                          (pict-height tm-pict)
                                          #:color "white"
                                          #:draw-border #f)
                        tm-pict)])]))

(define (present-hypothesis h)
  (match h
    [(hypothesis name assumption relevant?)
     (define name-p
       (new presentation-img%
            [object name]
            [modality '(name term)]
            [img (new pict-img% [pict (inset (text (format "~v" name)) 8)])]))
     (define colon (text " : "))
     (define assumption-p (present-term assumption))
     ;; TODO relevant? handling
     (new presentation-img%
          [object h]
          [modality '(hypothesis)]
          [img name-p])]
    ))

(define (present-goal g)
  (match g
    [(>> H G)
     (let ([hyps-pres (reverse (map present-hypothesis H))]
           [goal-pres (present-term G)])
       (error 'todo))]))

(define (present-step proof-step)
  (match proof-step
    [(dependent-subgoal waiting-for next)
     (error 'nope)]
    [(irrelevant-subgoal goal)
     (error 'nope)]
    [(subgoal name goal)
     (error 'nope2)]
    [(complete-proof goal rule extract children)
     (error 'nope44)]
    [(refined-step name goal rule children extractor)
     (error 'ĺkjlkj)]))

(define (prover-window namespace goal)
  (define proof-state
    (init-proof-state (new-goal goal)))

  (define (run-action act)
    (let-values ([(res new-state) (proof-run act proof-state)])
      (set! proof-state new-state)
      res))

  (define history (list proof-state))
  (define (checkpoint st)
    (set! history (cons st history)))
  (define (undo)
    (set! proof-state (car history))
    (set! history (cdr history)))

  (define frame (new frame%
                     [label "Pudding Prover"]
                     [width 800]
                     [height 600]))
  (define stack (new vertical-panel% [parent frame]))
  (define toolbar (new horizontal-panel% [parent stack] [stretchable-height #f]))
  (define horiz (new panel:vertical-dragable% [parent stack]))
  (define context (new panel:horizontal-dragable% [parent horiz]))
  (define node-context (new presentation-canvas% [parent context]))
  (define global-context (new tab-panel% [parent context]
                              [choices '("Program" "Proof")]))
  (define proof-script (new proof-script-text%
                            [advance-callback
                             (lambda (prog)
                               (define st proof-state)
                               (run-action (eval prog namespace))
                               (checkpoint st))]
                            [retract-callback undo]
                            [error-callback displayln]))
  (define proof-script-holder (new editor-canvas% [parent horiz] [editor proof-script]))
  (define retract-button
    (new button%
         [parent toolbar]
         [label "Retract"]
         [callback (thunk* (send proof-script retract))]))
  (define advance-button
    (new button%
         [parent toolbar]
         [label "Advance"]
         [callback (thunk* (send proof-script advance))]))

  (send frame show #t))

(module+ main
  (module stlc-prover-context racket/base
    (require "theories/stlc.rkt")
    (require "tactics.rkt")
    (require zippers)
    (require "proof-state.rkt")
    (require "proofs.rkt")

    (provide stlc-anchor g (rename-out [assumption stlc-assumption]))

    (define-namespace-anchor stlc-anchor)
    (define g #'(--> String Int)))

  (require
   'stlc-prover-context)

  (prover-window (namespace-anchor->namespace stlc-anchor) g))
