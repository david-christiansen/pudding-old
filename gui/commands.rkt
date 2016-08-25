#lang racket

(require (for-syntax syntax/parse racket/string)
          presentations
          pict
          "../error-handling.rkt"
          "pict-helpers.rkt")

(provide present-command (struct-out command) (struct-out command-app) (struct-out command-param))

(module+ test (require rackunit))

;;; A command is a verb in the system. It is what will be executed in
;;; the REPL.
;;;
;;; symbol-name is the name of the command as a symbol, to be used
;;; when calling it from Racket code, in things like error
;;; reports. The text name will be shown in the UI.
;;;
;;; The args should be a list of command args. Each command arg
;;; specifes a name, a presentation type, and a monadic predicate for
;;; acceptability.
;;;
;;; Finally, action should be an action in the proof monad.

(struct command-param (name type predicate) #:transparent)
(struct command (symbol-name text-name params action)
  #:property prop:procedure
  (lambda (c . arguments)
    (define remaining (- (length (command-params c)) (length arguments)))
    (if (< remaining 0)
        (raise-argument-error
         (command-symbol-name c)
         (format "~a or fewer arguments" (length (command-params c)))
         arguments)
        (command-app c
                     (append (map box arguments)
                             (build-list remaining (thunk* (box unspecified))))))))

(define-for-syntax (command-name sym)
  (string-titlecase (string-join (string-split (symbol->string sym) "-") " ")))

(begin-for-syntax
  (define-syntax-class command-param-spec
    #:attributes (name type predicate)
    (pattern (name:id type:expr)
             #:with predicate #'(lambda (x) (proof (pure #t))))
    (pattern (name:id type:expr predicate:expr))))

(define-syntax (define-command stx)
  (syntax-parse stx
    [(_ (n:id arg:command-param-spec ...) body ...+)
     (with-syntax ([text-name (command-name (syntax-e #'n))])
       #'(define n
           (command 'n
                    text-name
                    (list (command-param 'arg.name arg.type arg.predicate) ...)
                    (lambda (arg.name ...) (proof body ...)))))]))

(define unspecified
  ((lambda ()
     (struct unspecified ())
     (unspecified))))

(define (provided? x)
  (not (eq? (unbox x) unspecified)))

;;; A command application is a command that has been (perhaps
;;; partially) instantiated with arguments. These can be run.
(struct command-app (command arguments) #:transparent)

(define (command-app-saturated? app)
  (match-define (command-app (command _ _ params _) args) app)
  (and (= (length params) (length args))
       (andmap provided? args)))

(define/contract (run-command app)
  (-> (and/c command-app? command-app-saturated?) (proof/c any/c))
  (match-define (command-app (command _ _ _ proc) args) app)
  ;; TODO: check that each arg fits within the corresponding presentation type
  (if (andmap provided? args)
      (apply proc (map unbox args))
      (error "not all args provided"))) ;; TODO real exception type for GUI intervention

(define command/p
  (make-presentation-type 'command/p))

(define command-arg/p
  (make-presentation-type 'command-arg/p))

(define command-arg-slot/p
  (make-presentation-type 'command-arg-slot/p))

(define (arg-slot-pict name)
  (frame (text (format "~a" name) '(italic))))


(define/contract (present-command-arg renderer arg param canvas)
  (-> (-> any/c presentation-type? pict?)
      any/c
      command-param?
      (is-a?/c pict-presenter<%>)
      pict?)
  (match-define (command-param name type predictate) param)
  (if (provided? arg)
      (send canvas make-presentation arg command-arg-slot/p
            (thunk* (frame (text "?" '(italic))))
            hl)
      (renderer arg)))

(define/contract (present-command renderer cmd canvas)
  (-> (-> any/c presentation-type? pict?)
      (or/c command? command-app?)
      (is-a?/c pict-presenter<%>)
      void?)
  (match cmd
    [(? command?)
     (present-command (cmd))]
    [(command-app (command _ name params _) args)
     (send canvas make-presentation cmd command/p
           (thunk* (frame
                    (inset 5 (apply hc-append 3 (text name '(bold))
                                    (for/list ([arg args]
                                               [param params])
                                      (present-command-arg renderer arg param canvas)))))))]))

(module+ test
  (define-command (no-op)
    (pure (void)))
  (check-equal? (command-symbol-name no-op) 'no-op)
  (check-equal? (command-text-name no-op) "No Op")
  (check-equal? (command-params no-op) '())
  (check-true (procedure? (command-action no-op)))
  (check-true (proof-action? ((command-action no-op))))

  (define direction/p (make-presentation-type 'direction/p))

  (require (only-in "../proof-state.rkt" movement-possible?
                    init-proof-state
                    get-focus
                    move
                    refine
                    solve)
           (only-in zippers up))

  (define-command (go [direction direction/p movement-possible?])
    (move direction))

  (check-true (command-app? (go)))
  (check-false (command-app-saturated? (go)))
  (check-true (command-app? (go up)))
  (check-true (command-app-saturated? (go up)))

  (require "../define-rule.rkt" "../infrastructure.rkt" "../proofs.rkt")
  (define-rule (magic)
    (>> H t)
    ()
    0)
  (define-rule (more-magic)
    (>> H t)
    ([t* (>> H t)])
    (add1 t*))

  (define st (init-proof-state (>> null #'the-goal)))

  (define rule/p (make-presentation-type 'rule/p))

  (define-command (refine-goal [rule rule/p])
    (refine rule))

  (define prf-1
    (proof-eval (proof (run-command (refine-goal (more-magic)))
                       (run-command (no-op))
                       (run-command (go (down/proof)))
                       (run-command (refine-goal (magic)))
                       solve
                       (run-command (go up))
                       solve
                       get-focus)
                st))
  (check-equal? (syntax->datum (complete-proof-extract prf-1))
                '(add1 0)))
