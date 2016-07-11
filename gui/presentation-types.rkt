#lang racket
(require presentations
         (only-in syntax/id-set
                  immutable-bound-id-set
                  immutable-free-id-set))
(provide (all-defined-out))

(define metavariable/p (make-presentation-type 'metavariable/p))

(define proof-step/p (make-presentation-type 'proof-step/p))

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

(define binding/p
  (let ([bindings (make-weak-hasheq)])
    (lambda (id)
      (if id
          (hash-ref! bindings id (thunk (bound-identifier/p id)))
          unknown-identifier/p))))

(define expression/p
  (make-presentation-type 'expression/p))

