#lang racket

(require racket/gui)

(require zippers)
(require "error-handling.rkt" "infrastructure.rkt" "proof-state.rkt" "proofs.rkt")

(provide prover prover-in-frame)

(define (show-sequent s)
  (define show-h
    (match-lambda
      [(hypothesis n t relevant?)
       (if relevant?
           `(: ,(syntax->datum n) ,(syntax->datum t))
           `(:? ,(syntax->datum n) ,(syntax->datum t)))]))
  (match s
    [(>> H g)
     `(>> ,(reverse (map show-h H))
          ,(syntax->datum g))]))

(define goal-view-panel%
  (class vertical-panel%
    (init parent)
    (init-field [assumption-action #f])
    (super-new [parent parent]
               [stretchable-height #f])

    (define/public (update focus)
      (send this change-children (thunk* null))
      (if (proof-step? focus)
          (match (proof-step-goal focus)
            [(>> hyps todo)
             (for ([h (reverse hyps)]
                   [i (in-range (- (length hyps) 1) -1 -1)])
               (match-define (hypothesis name assumption relevant?) h)
               (define row (new horizontal-panel%
                                [parent this]
                                [stretchable-height #f]))
               (new button%
                    [parent row]
                    [label (format "~a: ~a" i (syntax->datum name))]
                    [enabled (and assumption-action
                                  relevant?
                                  (or (subgoal? focus)
                                      (irrelevant-subgoal? focus)))]
                    [callback (thunk* (assumption-action i))])
               (new message%
                    [parent row]
                    [label (format "~a" (syntax->datum assumption))])
               (void))
             (new message%
                  [parent this]
                  [label (format "~a" (syntax->datum todo))])])
          (new message% [parent this] [label (format "Oops: focus ~a" focus)])))))

(define children-panel%
  (class group-box-panel%
    (init-field parent)
    (init proof-runner)

    (super-new [parent parent]
               [label "Children"]
               [stretchable-height #f])

    (define (add-child-widget i name goal ready?)
      (define row (new horizontal-panel% [parent this]))
      (define button (new button%
                          [parent row]
                          [label name]
                          [enabled ready?]
                          [callback (thunk*
                                     (proof-runner (move down/proof-step-children
                                                         (down/list-ref i))))]))
      (define label (new message% [parent row]
                         [label (format "~a" (show-sequent goal))]))
      (void))

    (define (add-child i goal [ready? #t])
      (match goal
        [(dependent-subgoal var next)
         (add-child i (next var) #f)]
        [(irrelevant-subgoal g)
         (add-child-widget i "_" g ready?)]
        [(subgoal n g)
         (add-child-widget i (format "~a" n) g ready?)]
        [(complete-proof g r e c)
         (add-child-widget i "✓" g ready?)]
        [(refined-step n g r c e)
         (add-child-widget i (format "~a" n) g ready?)]))

    (define/public (update focus)
      (send this change-children (thunk* null))
      (send this show (and (or (refined-step? focus) (complete-proof? focus))
                           (pair? (proof-step-children focus))))
      (when (or (refined-step? focus)
                (complete-proof? focus))
        (for ([ch (proof-step-children focus)]
              [i (in-naturals)])
          (add-child i ch))))))

(define prover-pane%
  (class vertical-panel%
    (init-field parent proof-state)
    (init rule-namespace
          [assumption-rule #f])
    (super-new [parent parent])
        (define view-updates null)
    (define (update-views)
      ;; Do autosolve first, to make sure it happens before view updates
      (autosolver (send this run-action get-focus))
      (for ([updater view-updates])
        (updater (send this run-action get-focus))))
    (define (register-observer f)
      (set! view-updates (cons f view-updates)))

    ;; Apply an action in the proof monad
    (define/public (run-action act)
      (let-values ([(res new-state) (proof-run act proof-state)])
        (set-field! proof-state this new-state)
        res))

    (define (refine-with rule [input #f])
      (run-action (refine rule))
      (when (syntax? input)
        (run-action (proof (<- f get-focus)
                           (match f
                             [(refined-step n g _ c e)
                              (set-focus (refined-step n g input c e))]
                             [_ (pure (void))])))))

    (define (autosolver focus)
      (when (and (refined-step? focus)
                 (andmap complete-proof? (refined-step-children focus)))
        (run-action solve)))

    (define navbar (new horizontal-panel%
                        [parent this]
                        [stretchable-height #f]))

    (define movement-buttons '())

    (define (make-movement-button label direction)
      (let ([the-button
             (new button%
                  [parent navbar]
                  [label label]
                  [callback (lambda (button event)
                              (run-action (move direction))
                              (update-views))])])
        (set! movement-buttons (cons (cons the-button direction)
                                     movement-buttons))
        the-button))

    (define (update-movement-buttons)
      (for ([button+dir movement-buttons])
        (define button (car button+dir))
        (define dir (cdr button+dir))
        (send button enable
              (run-action (movement-possible? dir)))))

    (define up-button
      (let ([double-up
             (zipper-movement (lambda (z) (up (up z)))
                              (lambda (z) (and (can-move? up z)
                                               (can-move? up (up z)))))])
        (make-movement-button "Up" double-up)))
    (define left-button
      (make-movement-button "Left" left/list))
    (define right-button
      (make-movement-button "Right" right/list))

    (register-observer (thunk* (update-movement-buttons)))

    (define navbar-spacer
      (new pane%
           [parent navbar]
           [stretchable-height #f]
           [stretchable-width #t]))

    (define status
      (new message%
           [parent navbar]
           [label ""]
           [auto-resize #t]))
    (register-observer
     (lambda (focus)
       (send status set-label
             (match focus
               [(subgoal _ _) "Goal (Ready)"]
               [(dependent-subgoal v _) (format "Goal (depends on ~a)" v)]
               [(irrelevant-subgoal _) "Goal (Ready)"]
               [(? complete-proof?) "✓"]
               [(? refined-step?) "Refined"]
               [_ ""]))))


    (define spacer
      (new pane% [parent this] [stretchable-width #f] [stretchable-height #t]))

    (define goal-viewer
      (new goal-view-panel%
           [parent this]
           [assumption-action
            (if assumption-rule
                (lambda (x)
                  (run-action (refine (assumption-rule x)))
                  (update-views))
                #f)]))

    (register-observer
     (lambda (focus)
       (send goal-viewer update focus)))

    (define children-viewer
      (new children-panel%
           [parent this]
           [proof-runner (lambda (tac)
                           (run-action tac)
                           (update-views))]))

    (register-observer
     (lambda (focus)
       (send children-viewer update focus)))

    (define rule-input
      (new text-field%
           [parent this]
           [label "Refinement rule"]
           [callback
            (lambda (field evt)
              (when (eqv? (send evt get-event-type) 'text-field-enter)
                (with-handlers ([exn:fail? displayln]) ;; todo error display
                  (let ([input
                         (with-input-from-string (send field get-value)
                           read-syntax)])
                    (refine-with
                     (eval input rule-namespace)
                     input))
                  (update-views))))]))

    (register-observer
     (lambda (focus)
       (let ([refinable? (or (subgoal? focus)
                             (irrelevant-subgoal? focus))]
             [perhaps-val (if (refined-step? focus)
                              (refined-step-rule focus)
                              #f)])
         (send rule-input enable refinable?)
         (if perhaps-val
             (send rule-input set-value (format "~a" (syntax->datum perhaps-val)))
             (send rule-input set-value "")))))

    (define extract-view
      (new message%
           [label ""]
           [parent this]
           [auto-resize #t]))

    (define (update-extract-view focus)
      (define (get-extract f)
        (match f
          [(subgoal n g) (datum->syntax #f n)]
          [(complete-proof _ _ e _) e]
          [(dependent-subgoal waiting next)
           (update-extract-view (next waiting))]
          [(irrelevant-subgoal _) #'(void)]
          [(refined-step _ _ _ children extractor)
           (apply extractor
                  (for/list ([c children] #:when (not (irrelevant-subgoal? c)))
                    (get-extract c)))]))
      (send extract-view set-label
            (format "⇒ ~a" (syntax->datum (get-extract focus)))))

    (register-observer (lambda (focus) (update-extract-view focus)))

    (update-views)))

;;; Make a frame into a prover frame.
;;; This is useful for Slideshow.
(define (prover-in-frame frame
                         #:proof-state proof-state
                         #:rule-namespace rule-namespace
                         #:assumption-rule [assumption-rule #f])
  (new prover-pane%
       [parent frame]
       [proof-state proof-state]
       [rule-namespace rule-namespace]
       [assumption-rule assumption-rule]))

(define prover-frame%
  (class frame%
    (init proof-state
          rule-namespace
          assumption-rule
          [width 800] [height 600] [label "Proof Editor"])

    (super-new [width width] [height height] [label label])

    (new prover-pane%
         [parent this]
         [proof-state proof-state]
         [rule-namespace rule-namespace]
         [assumption-rule assumption-rule])))



(define (prover namespace goal #:assumption-rule [assumption-rule #f])
  (define frame (new prover-frame%
                     [proof-state (init-proof-state (new-goal goal))]
                     [rule-namespace namespace]
                     [assumption-rule assumption-rule]))
  (send frame show #t)
  (void))

(module+ test
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

  (define (test-prover)
    (prover (namespace-anchor->namespace stlc-anchor) g
            #:assumption-rule stlc-assumption)))
