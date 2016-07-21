#lang racket

(require syntax/parse (for-syntax syntax/parse))

(provide context
         hole
         (contract-out
          [context? (-> syntax? boolean?)]
          [fill (-> context? syntax? syntax?)]))

;; One-hole contexts are syntax objects that contain precisely one
;; hole.
(define-syntax hole
  (lambda (_)
    (raise-syntax-error 'hole "used outside context")))

;; Not identical to andmap/ormap when non-Boolean, and only takes one
;; list, but sufficient for our purposes here.
(define (xormap f l)
  (cond
    [(null? l) #t]
    [else (xor (f (car l))
               (xormap f (cdr l)))]))

(define/contract (context? stx)
  (-> syntax? boolean?)
  (syntax-parse stx
    #:literals (hole)
    [(expr ...)
     (xormap context? (syntax->list #'(expr ...)))]
    [#(expr ...)
     (xormap context? (syntax->list #'(expr ...)))]
    [#&expr
     (context? #'expr)]
    [hole
     #t]
    [_
     #f]))

(begin-for-syntax
  (define-literal-set context-lits (hole))

  (define-syntax-class complete-expr
    #:attributes (expr)
    #:literal-sets (context-lits)
    #:description "an expression without holes"
    (pattern (~and x:id (~not hole))
             #:with expr #'x)
    (pattern (e:complete-expr ...)
             #:with expr #'(e ...))
    (pattern #(e:complete-expr ...)
             #:with expr #'#(e ...))
    (pattern #&e:complete-expr
             #:with expr #'#&e)
    (pattern (~and expr
                   (~not x:id)
                   (~not (e ...))
                   (~not #(e ...))
                   (~not #&e))))

  (define-syntax-class context
    #:attributes (expr)
    #:literal-sets (context-lits)
    (pattern hole
             #:with expr #'hole)
    (pattern (before:complete-expr ... c:context after:complete-expr ...)
             #:with expr #'(before.expr ... c.expr after.expr ...))
    (pattern #(before:complete-expr ... c:context after:complete-expr ...)
             #:with expr #'#(before.expr ... c.expr after.expr ...))
    (pattern #&c:context
             #:with expr #'#&c.expr)))

(define-syntax (context stx)
  (syntax-parse stx
    [(_ c:context)
     #'(syntax c.expr)]))

(define (fill context stx)
  (syntax-parse context
    #:literals (hole)
    [(expr ...)
     (datum->syntax context
                    (map (lambda (c) (fill c stx))
                         (syntax->list #'(expr ...))))]
    [#(expr ...)
     (with-syntax ([(filled ...)
                    (map (lambda (c) (fill c stx))
                         (syntax->list #'(expr ...)))])
       #'#(filled ...))]
    [#&expr
     (with-syntax ([filled (fill #'expr stx)])
       #'#&filled)]
    [hole
     stx]
    [other
     #'other]))

(define-namespace-anchor context-anchor)

(module+ test
  (require rackunit)

  ;;; Test for parsing of contexts
  (parameterize ([current-namespace
                  (namespace-anchor->namespace context-anchor)])
    (check-exn exn:fail:syntax?
               (thunk (expand #'(context hole hole))))
    (check-exn exn:fail:syntax?
               (thunk (expand #'(context (+ hole hole)))))
    (check-exn exn:fail:syntax?
               (thunk (expand #'(context #(1 2 hole #&hole hole)))))
    (check-not-exn
     (thunk (expand #'(context hole))))
    (check-not-exn
     (thunk (expand #'(context (+ 1 hole 2)))))
    (check-not-exn
     (thunk (expand #'(context (+ 1 #&hole 3)))))
    (check-not-exn
     (thunk (expand #'(context #(1 2 hole x))))))

  ;;; Test substitution
  (check-equal? (syntax->datum (fill (context (x y hole z)) #'(foo)))
                '(x y (foo) z))
  (check-equal? (syntax->datum (fill (context (#&#(1 hole 2) 23)) #'7))
                `(,(box #(1 7 2)) 23))
  (check-equal? (syntax->datum (fill
                                (fill
                                 (context (+ 1 hole))
                                 (context (+ 2 hole)))
                                #'3))
                '(+ 1 (+ 2 3))))
