#lang racket

(require racket/gui framework presentations pict)
(require zippers)
(require (prefix-in pp: pprint))
(require syntax/parse)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt" "metavariables.rkt")

(define (hl pict)
  (frame pict))

(define (pprint-term stx canvas)
  (syntax-parse stx
    #:literals (lambda)
    [x:id
     (pp:markup
      (lambda (str)
        (if (string? str)
            (send canvas make-presentation #'x '(name)
                  (text str) hl)
            (send canvas make-presentation #'x '(name)
                  str hl)))
      (pp:text (symbol->string (syntax->datum #'x))))]
    [(lambda (xs:id ...) body)
     (pp:h-append
      pp:lparen
      (pp:v-concat/s
       (list (pp:group
              (pp:hs-append (pp:text "lambda")
                            pp:lparen
                            (apply pp:hs-append
                                   (map (lambda (t) (pprint-term t canvas))
                                        (syntax-e #'(xs ...))))
                            pp:rparen))
             (pprint-term #'body canvas)))
      pp:rparen)]
    #;
    [(? metavariable? (app syntax-e))
     (pp:markup
      (lambda (str)
        (send canvas make-presentation #'x '())))]
    [(tm ...)
     (pp:h-append pp:lparen
                  (pp:v-concat/s (map (lambda (t) (pprint-term t canvas))
                                      (syntax-e #'(tm ...))))
                  pp:rparen)]
    [other (pp:text (format "~v" (syntax->datum #'other)))]))

(define (term->pict stx canvas)
  (define (string->pict x)
    (if (string? x)
        (let ([lines (string-split x "\n" #:trim? #f)])
          (for/fold ([pict (blank)]) ([l lines])
            (vl-append pict (text l))))
        x))
  (pp:pretty-markup
   (pprint-term stx canvas)
   (lambda (x y)
     (hbl-append (string->pict x) (string->pict y)))
   70))

(define (extract-pict focus canvas)
  (define (get-extract f)
    (match f
      [(subgoal n g) (datum->syntax #f n)]
      [(complete-proof _ _ e _) e]
      [(dependent-subgoal waiting next)
       (get-extract (next waiting))]
      [(irrelevant-subgoal _) #'(void)]
      [(refined-step _ _ _ children extractor)
       (apply extractor
              (for/list ([c children] #:when (not (irrelevant-subgoal? c)))
                (get-extract c)))]))
  (term->pict (get-extract focus) canvas))

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


(define (vertically . imgs)
  (define h 0)
  (define todo
    (for/list ([i imgs])
      (define step
        (list 0 h i))
      (set! h (+ h (send i get-height)))
      step))
  (new compound-img% [imgs todo]))

(define (horizontally . imgs)
  (define w 0)
  (define todo
    (for/list ([i imgs])
      (define step
        (list w 0 i))
      (set! w (+ w (send i get-width)))
      step))
  (new compound-img% [imgs todo]))

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
          [img (horizontally name-p colon assumption-p)])]
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
  (define global-context (new tab-panel%
                              [parent context]
                              [choices '("Program" "Proof")]
                              [callback (lambda (panel ev)
                                          (when (eqv? (send ev get-event-type) 'tab-panel)
                                            (match (send global-context get-selection)
                                              [0 (send global-context change-children
                                                       (thunk* (list program-view)))]
                                              [1 (send global-context change-children
                                                       (thunk* (list proof-view)))]
                                              [other (error "Unknown tab")])))]))
  (define program-view (new presentation-pict-canvas%
                            [parent global-context]))
  (define proof-view (new presentation-pict-canvas%
                          [parent global-context]))
  (define proof-script (new proof-script-text%
                            [advance-callback
                             (lambda (prog)
                               (define st proof-state)
                               (run-action (eval prog namespace))
                               (checkpoint st))]
                            [retract-callback undo]
                            [error-callback displayln]))
  (define proof-script-holder (new editor-canvas% [parent horiz] [editor proof-script]))

  (define (update-views)
    (define focus (run-action get-focus))
    (send program-view remove-all-picts)
    (send program-view add-pict (extract-pict focus program-view) 5 5))

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
