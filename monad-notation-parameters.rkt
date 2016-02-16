#lang racket

;;; Due to a present limitation in Typed Racket, syntax parameters
;;; defined in a TR module cannot be used in another TR module. So we
;;; define them in an untyped module, then re-export them from the
;;; typed module.

(require racket/stxparam)

(provide current-monad current-pure <-)

(define-syntax-parameter current-monad
  (lambda (stx)
    (raise-syntax-error 'current-monad "no current monad" stx)))

(define-syntax-parameter current-pure
  (lambda (stx)
    (raise-syntax-error 'pure "no current pure op" stx)))

;;; Similarly, it seems that literals to be matched across modules in
;;; a syntax-parse rule must also be defined in an untyped module

(define-syntax (<- stx)
 (raise-syntax-error '<- "used outside of do" stx))
