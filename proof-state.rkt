#lang racket

(require (rename-in "error-handling.rkt"
                    [proof-get get]
                    [proof-put put]
                    [proof-modify modify])
         "metavariables.rkt")

(provide init-proof-state
         new-meta
         lookup-meta
         instantiated?
         uninstantiated?)



;;; A proof tree zipper is represented as a list of "frames", where
;;; the top of the tree is the end of the list.
(struct proof-zipper-frame ()
  )

;;; A proof state contains:
;;;
;;;  1. A name supply (here represented as a metavariable context)
;;;  2. A Huet zipper into a proof tree
(struct proof-state
  (metavariables))

(define (set-metavariables st new-ctxt)
  (proof-state new-ctxt))

(define (init-proof-state)
  (proof-state (fresh-context)))

(define/proof (new-meta hint)
  (<- st get)
  (let old-ctxt (proof-state-metavariables st))
  (let-values (new-ctxt var) (new-metavariable old-ctxt hint))
  (put (set-metavariables st new-ctxt))
  (pure var))

(define/proof (lookup-meta var)
  (<- (proof-state ctxt) get)
  (pure (lookup-metavariable ctxt var)))

(struct exn:fail:metavariable-already-assigned exn:fail:contract
  (metavariable context)
  #:extra-constructor-name make-exn:fail:metavariable-already-assigned
  #:transparent)

(define (assign-meta var stx)
  (proof
   (<- (proof-state ctxt) get)
   (let val (lookup-metavariable ctxt var))
   (if (instantiated? val)
       (proof-fail (make-exn:fail:metavariable-already-assigned
                    "Metvariable already assigned"
                    (current-continuation-marks)
                    var
                    ctxt))
       (proof (let new-ctxt (assign var stx ctxt))
              (set-metavariables new-ctxt)))))

