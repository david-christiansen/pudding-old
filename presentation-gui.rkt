#lang racket

(require racket/gui framework presentations pict)
(require zippers)
(require syntax/parse)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt" "metavariables.rkt" "expand-bindings.rkt" "standard-resources.rkt")
(require macro-debugger/expand)
(require macro-debugger/syntax-browser)
(require macro-debugger/stepper)

(require "gui/commands.rkt" "gui/presentation-types.rkt" "gui/proof-pict.rkt" "gui/sequent-pict.rkt" "gui/term-pict.rkt" "gui/pict-helpers.rkt")

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

(define/contract (sequent->big-pict seq canvas [extract #f])
  (->* (sequent?
        (is-a?/c presentation-pict-canvas%))
       ((or/c #f syntax?))
       pict-convertible?)
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
       (send canvas make-presentation G goal/p
             (lambda (G)
               (hb-append
                7
                (if (syntax? extract)
                    (hb-append 7 (term->pict extract canvas (map hypothesis-name H))
                               (text ":"))
                    (text "Goal:"))
                (term->pict G canvas (map hypothesis-name H))))
             hl))
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


(define rule/p
  (make-presentation-type 'rule/p))

(define rule-argument/p
  (make-presentation-type 'rule-argument/p))

(define rule-argument-name/p
  (make-presentation-type 'rule-argument-name/p))

(define (present-rule rule canvas)
  (let ([to-present
         (cond
           [(rule-application? rule)
            rule]
           [(refinement-rule? rule)
            (rule)]
           [else (raise-argument-error
                  'present-rule
                  rule
                  "refinement rule")])])
    (send canvas make-presentation to-present rule/p
          (lambda (r)
            (match-define (rule-application (refinement-rule name params _)
                                            args)
              to-present)
            (define name-pict (text (format "~a" name) '(bold)))
            (define args-picts
              (for/list ([arg-box args]
                         [param params])
                (send canvas make-presentation arg-box
                      (match (rule-parameter-sort param)
                        ['name rule-argument-name/p]
                        [_ rule-argument/p])
                      (lambda (presented-arg-box)
                        (define arg (unbox presented-arg-box))
                        (if (provided? arg)
                            (text (format "~a" arg))
                            (text (format "~a:~a"
                                          (rule-parameter-name param)
                                          (rule-parameter-sort param))
                                  '(italic))))
                      hl)))
            (frame (inset (apply hc-append 8 name-pict args-picts) 3)))
          hl)))

(define (generic-intro)
  (let loop ([tactics (intro-tactics)])
    (if (null? tactics)
        (proof-error "No applicable introduction rules")
        (handle-errors (car tactics)
          [_ (loop (cdr tactics))]))))

(define (prover-window namespace goal)
  (define proof-state
    (init-proof-state (new-goal goal)))

  (define (run-action act)
    (let-values ([(res new-state) (proof-run act proof-state)])
      (set! proof-state new-state)
      res))

  (parameterize ()
    (define history (list proof-state))
    (define (checkpoint st)
      (set! history (cons st history)))
    (define (undo)
      (set! proof-state (car history))
      (set! history (cdr history)))

    (define (on-error e)
      (send error-view remove-all-picts)
      (send error-view add-pict (text (exn-message e)) 5 5)
      (displayln e)
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

    (define transparent-yellow
      (let* ([solid-yellow (make-object color% "yellow")]
             [r (send solid-yellow red)]
             [g (send solid-yellow green)]
             [b (send solid-yellow blue)])
        (make-object color% r g b 0.2)))

    (define (repl-callback input-str)
      (with-handlers ([exn:fail? on-error])
        (send error-view remove-all-picts)
        (define result
          (eval (with-input-from-string input-str (thunk (read)))
                namespace))
        (cond
          [(or (command? result) (command-app? result))
           (let ([snip (new presentation-pict-snip%)])
             (send snip add-pict (present-command result snip) 1 1)
             snip)]
          [(or (refinement-rule? result) (rule-application? result))
           (let ([snip (new presentation-pict-snip%)])
             (send snip add-pict (present-rule result snip) 1 1)
             snip)]
          [(proof-action? result)
           (run-action result)
           (update-views)]
          [else
           (pstring (format "~a" result))])))

    (define repl
      (new presentation-repl%
           [highlight-callback (lambda (dc x1 y1 x2 y2)
                                 (define old-brush (send dc get-brush))
                                 (define old-pen (send dc get-pen))
                                 (send* dc
                                   (set-brush transparent-yellow)
                                   (set-pen transparent-yellow 4 'solid)
                                   (draw-rectangle x1 y1 x2 y2)
                                   (set-brush old-brush)
                                   (set-pen old-pen)))]
           [eval-callback repl-callback]))

    (define repl-canvas
      (new editor-canvas% [parent horiz] [editor repl]))

    (define (update-views)
      (define (get-extract s)
        (match s
          [(? complete-proof?)
           (complete-proof-extract s)]
          [(with-path _ s)
           (get-extract s)]
          [_ #f]))
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
              (sequent->big-pict (proof-step-goal focus) node-context (get-extract focus))
              5 5))
      (update-buttons))

    (define (update-buttons)
      (void))

    (send (current-presentation-context) register-command-translator rule/p
          (lambda (rule)
            (list (list "Refine goal" (thunk (run-action (refine rule))
                                             (update-views))))))

    (send (current-presentation-context) register-command-translator proof-step/p
          (lambda (step)
            (define (solved? s)
              (match s
                [(with-path _ inner)
                 (solved? inner)]
                [(? complete-proof?)
                 #t]
                [_ #f]))
            (define (all-solved? ss)
              (andmap solved? ss))
            (append
             (match step
               [(with-path (? pair? path) step)
                (list
                 (list "Move here" (thunk (run-action (for/proof ([direction path])
                                                        (move direction)))
                                          (update-views))))]
               [_ (list)])
             (match step
               [(with-path path (refined-step _ _ _ (app all-solved? ok) _))
                #:when ok
                (list
                 (list "Solve" (thunk
                                (run-action (proof (for/proof ([direction path])
                                                     (move direction))
                                                   solve))
                                (update-views))))]
               [_ (list)]))))

    (send (current-presentation-context) register-default-command proof-step/p
          (lambda (step)
            (match step
              [(with-path (? pair? path) step)
               (run-action (for/proof ([direction path])
                             (move direction)))
               (update-views)]
              [_ (void)])))

    (send (current-presentation-context) register-command-translator goal/p
          (lambda (g)
            (list (list "Intro" (thunk (run-action (generic-intro))
                                       (update-views))))))

    (update-views)

    (send frame show #t)
    ;; After show because otherwise the secondary tabs are first drawn
    ;; when they are shown during a window resize. This would be nice to
    ;; diagnose and fix!
    (set-tab 0)))

(define (display-binding id [parent #f])
  (match (identifier-binding id)
    [(list source-mod
           source-id
           nominal-source-mod
           nominal-source-id
           source-phase
           import-phase
           nominal-export-phase)
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

(send (current-presentation-context) register-command-translator rule-argument-name/p
      (lambda (arg-box)
        (define (new-name)
          (define (valid-symbol? str)
            (with-handlers ([exn:fail? (thunk* #f)])
              (symbol? (with-input-from-string str
                         (thunk (read))))))
          (define str
            (get-text-from-user "What name?"
                                "Provide a name."
                                #f
                                ""
                                '(disallow-invalid)
                                #:validate valid-symbol?))
          (when (string? str)
            (define x (with-input-from-string str
                        (thunk (read))))
            (if (symbol? x)
                (set-box! arg-box x)
                (error "Not a name")))
          (send (current-presentation-context) mutation))
        (if (provided? (unbox arg-box))
            (list
             (list "Replace name" new-name))
            (list
             (list "Provide name" new-name)))))



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
    (define g2 #'(=-in ((lambda (y) y) (Type 0)) (Type 0) (Type 1)))
    #;
    (define g2 #'(--> (Boolean) (--> (String) (--> (String) (String))))))

  (require
   'stlc-prover-context)

  (parameterize ([current-namespace (namespace-anchor->namespace stlc-anchor)])
    (prover-window (namespace-anchor->namespace stlc-anchor)
                   (decorate-identifiers g)))

  (require
   'ctt-prover-context)
#;
  (parameterize ([current-namespace (namespace-anchor->namespace ctt-anchor)])
    (prover-window (namespace-anchor->namespace ctt-anchor) (decorate-identifiers g2))))
