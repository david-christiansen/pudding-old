#lang racket

(require racket/gui framework presentations pict)
(require zippers)
(require (prefix-in pp: pprint))
(require syntax/parse
         (only-in syntax/id-set immutable-bound-id-set immutable-free-id-set))
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt" "metavariables.rkt" "expand-bindings.rkt")
(require macro-debugger/expand)
(require framework)

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

;; Highlights
(define/contract (hl pict)
  (-> pict? pict?)
  (let ([w (pict-width pict)]
        [h (pict-height pict)])
    (frame (cc-superimpose
            pict
            (cellophane
             (filled-rectangle w h
                               #:draw-border? #f
                               #:color "yellow")
             0.2))
           #:color "yellow")))

;; Here id is an opaque notion of identification, really just needed
;; for debugging, because make-presentation-type is generative.
(define (bound-identifier/p id)
  (make-presentation-type 'bound-identifier/p
                          #:equiv? (lambda (x y)
                                     (and (identifier? x)
                                          (identifier? y)
                                          (bound-identifier=? x y)))
                          #:empty-set immutable-bound-id-set))
(define free-identifier/p
  (make-presentation-type 'free-identifier/p
                          #:equiv? (lambda (x y)
                                     (and (identifier? x)
                                          (identifier? y)
                                          (free-identifier=? x y)))
                          #:empty-set immutable-free-id-set))
(define unknown-identifier/p
  (make-presentation-type 'unknown-identifier/p))

(define proof-step/p (make-presentation-type 'proof-step/p))

(define metavariable/p (make-presentation-type 'metavariable/p))

(define binding/p
  (let ([bindings (make-weak-hasheq)])
    (lambda (id)
      (if id
          (hash-ref! bindings id (thunk (bound-identifier/p id)))
          unknown-identifier/p))))

(define/contract (hyp->pict h canvas prev)
  (-> hypothesis?
      (is-a?/c presentation-pict-canvas%)
      (listof hypothesis?)
      pict?)
  (match h
    [(hypothesis name assumption relevant?)
     (define h-id (get-occurrence-id name))
     (define name-pict
       (send canvas make-presentation name (binding/p h-id)
             (text (format "~a" (syntax-e name)))
             hl))
     (define assumption-pict
       (term->pict assumption canvas (map hypothesis-name prev)))
     (define (wrap p)
       (if relevant?
           p
           (hb-append (text "[") p (text "]"))))
     (wrap (hb-append name-pict (text " : ") assumption-pict))]))

(define/contract (sequent->pict seq canvas)
  (-> sequent? (is-a?/c presentation-pict-canvas%) pict?)
  (match seq
    [(>> H G)
     (define H-pict
       (if (null? H)
           (cc-superimpose
            (ghost (text "()"))
            (filled-ellipse 3 3 #:color "black"))
           (apply hb-append
                  (add-between (reverse
                                (let loop ([hyps H])
                                  (if (null? hyps)
                                      '()
                                      (cons (hyp->pict (car hyps) canvas (cdr hyps))
                                            '() #;(loop (cdr hyps))
                                            ))))
                               (text ", ")))))
     (define G-pict
       (term->pict G canvas (map hypothesis-name H)))
     (hb-append H-pict (text " >> ") G-pict)]))

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

(define (on-box pict #:color [color "white"] #:border-width [border-width #f])
  (cc-superimpose (filled-rectangle (pict-width pict) (pict-height pict) #:color color #:border-width border-width)
                  pict))

(define (opaque pict)
  (cc-superimpose (filled-rectangle (pict-width pict) (pict-height pict)
                                    #:color "white"
                                    #:draw-border? #f)
                  pict))

;;; Given a proof zipper, return a procedure that takes a pict
;;; representing the focus and its indentation and returns a pict
;;; representing the whole tree.

(define proof-vspace 10)

(define (indent-proof-pict p)
  (define indent-space 20)
  (inset p indent-space 0 0 0))

(define (proof-context->pict->pict ctxt canvas)
  (lambda (focus-pict)
    (match ctxt
      [(list)
       focus-pict]
      [(cons (list-item-frame to-left to-right) more)
       (define before
         (map (lambda (p) (proof->pict (decorate-proof p) canvas))
              (reverse to-left)))
       (define after
         (map (lambda (p) (proof->pict (decorate-proof p) canvas))
              to-right))
       (define siblings
         (apply vl-append proof-vspace
                (append before (list focus-pict) after)))
       ((proof-context->pict->pict more canvas)
        siblings)]
      [(cons prf-frame more)
       (match-define (zipper wrapped new-ctxt)
         (up (zipper focus-pict (cons prf-frame more))))
       ((proof-context->pict->pict new-ctxt canvas)
        (proof->pict wrapped canvas))])))

(define/contract (proof->pict proof canvas #:focus? [focus? #f])
  (->* (proof-step? (is-a?/c presentation-pict-canvas%))
       (#:focus? boolean?)
       pict?)
  (define hspace 5)
  (define by (text "by" '(bold)))
  (define left (text "<=" '(bold)))
  (define bw (if focus? 3 #f))
  (define (mv n)
    (send canvas make-presentation n metavariable/p
          (opaque (text (format "~v" n)))
          hl))
  (define/contract (with-children step pict)
    (-> proof-step?
        pict?
        pict?)
    (match step
      [(or (refined-step _ _ _ children _)
           (complete-proof _ _ _ children))
       (apply vl-append proof-vspace pict
              (if (pict? children)
                  (list (indent-proof-pict children))
                  (for/list ([c children])
                    (indent-proof-pict (proof->pict c canvas)))))]
      [_ pict]))
  (define/contract step-pict
    pict?
    (match proof
      [(subgoal name goal)
       (define status (text "?" '(bold)))
       (define n (mv name))
       (define p (inset (hb-append
                         hspace
                         status
                         n
                         left
                         (sequent->pict goal canvas))
                        3))
       (on-box p #:border-width bw)]
      [(refined-step name (>> H G) rule children extractor)
       (define status (text "➥" '(bold)))
       (define n (mv name))
       (define p
         (inset (hb-append hspace
                           status
                           n
                           left
                           (sequent->pict (>> H G) canvas)
                           (if rule
                               (hb-append hspace
                                          by
                                          (term->pict
                                           (datum->syntax #f rule)
                                           canvas
                                           (map hypothesis-name H)))
                               empty))
                3))
       (on-box p #:border-width bw)]
      [(complete-proof (>> H G) rule extract children)
       (define status (text "✔" '(bold)))
       (inset (hb-append hspace
                         status
                         (term->pict extract canvas (map hypothesis-name H))
                         left
                         (sequent->pict (>> H G) canvas))
              3)]
      [(? pict? a-pict)
       ;; This is a bit of a hack, but it lets this be easily used
       ;; with the zipper-traversing code
       a-pict]
      [other (on-box (text (format "~v" other)))]))
  (send canvas make-presentation proof proof-step/p
        (with-children proof step-pict)
        hl))

(define (pprint-term stx canvas bindings)
  (-> syntax?
      (is-a?/c presentation-pict-canvas%)
      (listof (cons/c symbol?
                       (or/c (list/c 'bound symbol?)
                             (list/c 'bound #f)
                             (list/c 'free)
                             (list/c 'binding))))
      any/c)
  (syntax-parse stx
    #:literals (lambda)
    [x:id
     (define x-id (get-occurrence-id #'x))
     (define p-type
       (cond [x-id
              (match (assoc x-id bindings)
                [(list _ 'bound binder-id) (binding/p binder-id)]
                [(list _ 'free) free-identifier/p]
                [(list _ 'binding) (binding/p x-id)]
                [#f
                 (displayln `(what is ,(syntax->datum #'x)))
                 unknown-identifier/p])]
             [(list? (identifier-binding #'x))
              free-identifier/p]
             [else unknown-identifier/p]))
     (pp:markup
      (lambda (str)
        (if (string? str)
            (send canvas make-presentation #'x p-type
                  (opaque (text str)) hl)
            (send canvas make-presentation #'x p-type
                  str hl)))
      (pp:text (symbol->string (syntax->datum #'x))))]
    [x #:when (metavariable? (syntax-e #'x))
       (pp:markup
        (lambda (str)
          (send canvas make-presentation (syntax-e #'x) metavariable/p
                (if (string? str) (opaque (text str)) str)
                hl))
        (pp:text (format "~v" (syntax-e #'x))))]
    #;
    [(lambda (xs:id ...) body)
     (pp:h-append
      pp:lparen
      (pp:v-concat/s
       (list (pp:group
              (pp:hs-append (pprint-term #'lambda canvas)
                            pp:lparen
                            (apply pp:hs-append
                                   (map (lambda (t) (pprint-term t canvas))
                                        (syntax-e #'(xs ...))))
                            pp:rparen))
             (pprint-term #'body canvas)))
      pp:rparen)]
    [(tm ...)
     (pp:h-append pp:lparen
                  (pp:v-concat/s (map (lambda (t) (pprint-term t canvas bindings))
                                      (syntax-e #'(tm ...))))
                  pp:rparen)]
    [other
     (pp:text (format "~v" (syntax->datum #'other)))]))

(define/contract (term->pict stx canvas bound-identifiers)
  (-> syntax? (is-a?/c presentation-pict-canvas%) (listof identifier?) pict?)
  (define (string->pict x)
    (if (string? x)
        (let ([lines (string-split x "\n" #:trim? #f)])
          (for/fold ([pict (blank)]) ([l lines])
            (vl-append pict (opaque (text l)))))
        x))
  ;; TODO put expand in the right namespace
  (define bindings (find-bindings (expand stx) bound-identifiers))
  (pp:pretty-markup
   (pprint-term stx canvas bindings)
   (lambda (x y)
     (hb-append (string->pict x) (string->pict y)))
   70))

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

  (require
   'stlc-prover-context)

  (prover-window (namespace-anchor->namespace stlc-anchor) (decorate-identifiers g)))
