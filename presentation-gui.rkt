#lang racket

(require racket/gui framework presentations pict)
(require zippers)
(require syntax/parse)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt" "metavariables.rkt" "expand-bindings.rkt")
(require macro-debugger/expand)
(require macro-debugger/syntax-browser)
(require macro-debugger/stepper)

(require "gui/presentation-types.rkt" "gui/proof-pict.rkt" "gui/sequent-pict.rkt" "gui/term-pict.rkt")

;; Binding stuff
(define/contract (decorate-hyp h)
  (-> hypothesis? hypothesis?)
  (match h
    [(hypothesis name assumption relevant?)
     (hypothesis (decorate-identifiers name) (decorate-identifiers assumption) relevant?)]))

(define (decorate-sequent g)
  (-> sequent? sequent?)
  (match g
    [(>> H G)
     (>> (map decorate-hyp H) (decorate-identifiers G))]))

(define/contract (decorate-proof p)
  (-> proof-step? proof-step?)
  (match p
    [(dependent-subgoal waiting-for next)
     (dependent-subgoal waiting-for (lambda (ext) (decorate-proof (next ext))))]
    [(irrelevant-subgoal goal)
     (irrelevant-subgoal (decorate-sequent goal))]
    [(subgoal name goal)
     (subgoal name (decorate-sequent goal))]
    [(complete-proof goal rule extract children)
     (complete-proof (decorate-sequent goal)
                     rule
                     (decorate-identifiers extract)
                     (map decorate-proof children))]
    [(refined-step name goal rule children extractor)
     (refined-step name
                   (decorate-sequent goal)
                   rule
                   (map decorate-proof children)
                   (lambda args (decorate-identifiers (apply extractor args))))]))






(define/contract (sequent->big-pict seq canvas)
  (-> sequent? (is-a?/c presentation-pict-canvas%) pict?)
  (match seq
    [(>> H G)
     (define context-pict
       (apply vl-append
              5
              (reverse
               (let loop ([hyps H])
                 (if (null? hyps)
                     '()
                     (cons (hyp->pict (car hyps) canvas (cdr hyps))
                           (loop (cdr hyps))))))))
     (define goal-pict
       (term->pict G canvas (map hypothesis-name H)))
     (define width (max (pict-width context-pict) (pict-width goal-pict)))
     (define line (filled-rectangle width 1 #:draw-border? #t))
     (vl-append 10 context-pict line goal-pict )]))




(define/contract (extract-pict focus canvas)
  (-> proof-step? (is-a?/c presentation-pict-canvas%) pict?)
  (define (get-extract+hyp-names f)
    (match f
      [(subgoal n (>> H _))
       (values (datum->syntax #f n)
               (map hypothesis-name H))]
      [(complete-proof (>> H _) _ e _)
       (values e (map hypothesis-name H))]
      [(dependent-subgoal waiting next)
       (get-extract+hyp-names (next waiting))]
      [(irrelevant-subgoal (>> H _))
       (values #'(void) (map hypothesis-name H))]
      [(refined-step _ (>> H _) _ children extractor)
       (values (apply extractor
                      (for/list ([c children] #:when (not (irrelevant-subgoal? c)))
                        (define-values (e h) (get-extract+hyp-names c))
                        e))
               (map hypothesis-name H))]
      [_ (blank)]))
  (define-values (ext hyp-names) (get-extract+hyp-names focus))
  (term->pict ext canvas hyp-names))

(define (read-with-length-from str)
  (define port (open-input-string str))
  (define output (read port))
  (values output (file-position port)))

(define proof-script-text%
  (class text%
    (init-field advance-callback retract-callback error-callback)
    (super-new)

    (inherit change-style
             get-text
             last-position
             set-position)

    (send this set-styles-sticky #f)

    ;; Style for accepted region and editable region
    (define accepted-bg
      (send (make-object style-delta%) set-delta-background
            "green"))

    (define editable-bg
      (send (make-object style-delta%) set-delta-background
            "white"))

    ;; The editor positions that constitute the ends of each accepted
    ;; proof step. When advancing the accepted region, the new
    ;; position is consed on to this.
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

    (define/public (can-advance?)
      (for/or ([ch (in-string (get-text (car steps) 'eof #t))])
        (not (char-whitespace? ch))))

    (define/public (can-retract?)
      (and (pair? steps)
           (pair? (cdr steps))))

    ;; Run a command
    (define/public (advance)
      (with-handlers ([exn? error-callback])
        (define step (car steps))
        (define text (get-text step))
        (define-values (val len) (read-with-length-from text))
        (queue-callback (thunk
                         (with-handlers ([exn? error-callback])
                           (advance-callback val)
                           (set-position (+ step len))
                           (save-step! (+ step len))
                           (queue-callback (thunk (update-bg))))))))

    (define/public (retract)
      (when (and (pair? steps) (pair? (cdr steps)))
        (set! steps (cdr steps))
        (queue-callback (thunk (update-bg)))
        (queue-callback (thunk (retract-callback)))))))


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

  (define (on-error e)
    (send error-view remove-all-picts)
    (send error-view add-pict (text (exn-message e)) 5 5)
    (send global-context set-selection 2)
    (set-tab 2))

  (define current-tab 0)
  (define (update-tab)
    (match current-tab
      [0 (send global-context change-children
               (thunk* (list program-view)))
         (queue-callback (thunk (send program-view refresh)))]
      [1 (send global-context change-children
               (thunk* (list proof-view)))
         (queue-callback (thunk (send proof-view refresh)))]
      [2 (send global-context change-children
               (thunk* (list error-view)))
         (queue-callback (thunk (send error-view refresh)))]
      [other (error "Unknown tab")]))
  (define (set-tab i)
    (set! current-tab i)
    (update-tab))

  (define frame
    (new frame%
         [label "Pudding Prover"]
         [width 800]
         [height 600]))
  (define menu
    (new menu-bar% [parent frame]))
  (define edit-menu
    (new menu% [parent menu] [label "Edit"]))
  (append-editor-operation-menu-items edit-menu)
  (define stack
    (new vertical-panel% [parent frame]))
  (define toolbar
    (new horizontal-panel% [parent stack] [stretchable-height #f]))
  (define horiz
    (new panel:vertical-dragable% [parent stack]))
  (define context
    (new panel:horizontal-dragable% [parent horiz]))
  (define node-context
    (new presentation-pict-canvas% [parent context]))
  (define global-context
    (new tab-panel%
         [parent context]
         [choices '("Program" "Proof" "Error")]
         [callback (lambda (panel ev)
                     (when (eqv? (send ev get-event-type) 'tab-panel)
                       (set-tab (send global-context get-selection))))]))
  (define program-view
    (new presentation-pict-canvas%
         [parent global-context]))
  (define proof-view
    (new presentation-pict-canvas%
         [parent global-context]))
  (define error-view
    (new presentation-pict-canvas%
         [parent global-context]))
  (define proof-script
    (new (class proof-script-text%
           (super-new)
           (define/override (on-char ev)
             (update-buttons)
             (super on-char ev)))
         [advance-callback
          (lambda (prog)
            (send error-view remove-all-picts)
            (define st proof-state)
            (run-action (eval prog namespace))
            (checkpoint st))]
         [retract-callback undo]
         [error-callback on-error]))

  (define proof-script-keymap
    (let ([map (send proof-script get-keymap)])
      (add-editor-keymap-functions map)
      (add-text-keymap-functions map)
      (send map add-function "advance" (thunk* (send proof-script advance)
                                               (queue-callback update-views)))
      (send map add-function "retract" (thunk* (send proof-script advance)
                                               (queue-callback update-views)))
      (for/list ([key '(("m:n" "advance")
                        ("m:p" "retract")
                        ("c:n" "next-line")
                        ("c:p" "previous-line")
                        ("m:v" "previous-page")
                        ("c:v" "next-page")
                        ("c:f" "forward-character")
                        ("c:b" "backward-character")
                        ("m:f" "forward-word")
                        ("m:b" "backward-word")
                        ("c:a" "beginning-of-line")
                        ("c:e" "end-of-line")
                        ("s:m:>" "end-of-file")
                        ("s:m:<" "beginning-of-file")
                        ("c:w" "cut-clipboard")
                        ("m:w" "copy-clipboard")
                        ("c:y" "paste-clipboard"))])
        (send map map-function (car key) (cadr key)))

      map))

  (define proof-script-holder
    (new editor-canvas% [parent horiz] [editor proof-script]))

  (define (update-views)
    (define z (run-action get-zipper))
    (define focus (zipper-focus z))
    (send program-view remove-all-picts)
    (send program-view add-pict (extract-pict focus program-view) 5 5)
    (send proof-view remove-all-picts)
    (send proof-view add-pict
          ((proof-context->pict->pict (zipper-context z) proof-view)
           (proof->pict (decorate-proof focus) proof-view #:focus? #t))
          5 5)
    (send node-context remove-all-picts)
    (with-handlers ([exn? displayln])
      (send node-context add-pict
            (sequent->big-pict (proof-step-goal focus) node-context)
            5 5))
    (update-buttons))

  (define (update-buttons)
    (send advance-button enable (send proof-script can-advance?))
    (send retract-button enable (send proof-script can-retract?)))

  (define retract-button
    (new button%
         [parent toolbar]
         [label "Retract"]
         [callback (thunk* (send proof-script retract)
                           (queue-callback update-views))]))
  (define advance-button
    (new button%
         [parent toolbar]
         [label "Advance"]
         [callback (thunk* (send proof-script advance)
                           (queue-callback update-views))]))

  (update-views)

  (send frame show #t)
  ;; After show because otherwise the secondary tabs are first drawn
  ;; when they are shown during a window resize. This would be nice to
  ;; diagnose and fix!
  (set-tab 0))

(define (display-binding id [parent #f])
  (match (identifier-binding id)
    [(list source-mod source-id nominal-source-mod nominal-source-id source-phase import-phase nominal-export-phase)
     (message-box (format "Info: ~s" (syntax-e id))
                  (format "Name: ~s\nSource module: ~s"
                          (syntax-e id)
                          source-mod))]
    [other (message-box (format "No info for ~s" (syntax-e id))
                        (format "There is no global binding information for ~s."
                                (syntax-e id))
                        parent
                        '(caution ok))]))

(send (current-presentation-context) register-command-translator free-identifier/p
      (lambda (id)
        (list (list "Binding information" (thunk (display-binding id)
                                                 (void))))))

(send (current-presentation-context) register-command-translator expression/p
      (lambda (val)
          (if (syntax? val)
              (list
               (list "Macro Stepper" (thunk (expand/step val)))
               (list "Syntax Browser" (thunk (browse-syntax val))))
              (list))))


(module+ main
  (module stlc-prover-context racket/base
    (require "theories/stlc.rkt")
    (require "tactics.rkt")
    (require zippers)
    (require "proof-state.rkt")
    (require "proofs.rkt")

    (provide stlc-anchor g (rename-out [assumption stlc-assumption]))

    (define-namespace-anchor stlc-anchor)
    (define g #'(--> String (--> String Int))))

  (module ctt-prover-context racket/base
    (require "theories/ctt.rkt")
    (require "tactics.rkt")
    (require zippers)
    (require "proof-state.rkt")
    (require "proofs.rkt")

    (provide ctt-anchor g2)

    (define-namespace-anchor ctt-anchor)
    (define g2 #'(--> Boolean (--> String (--> String String)))))

  (require
   'stlc-prover-context)
  (parameterize ([current-namespace (namespace-anchor->namespace stlc-anchor)])
    (prover-window (namespace-anchor->namespace stlc-anchor) (decorate-identifiers g)))


  (require
   'ctt-prover-context)

  (parameterize ([current-namespace (namespace-anchor->namespace ctt-anchor)])
    (prover-window (namespace-anchor->namespace ctt-anchor) (decorate-identifiers g2))))
