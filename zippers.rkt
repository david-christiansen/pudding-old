#lang racket

(require (for-syntax racket/list
                     syntax/parse
                     racket/struct-info
                     racket/syntax)
         racket/provide-syntax)

(provide (struct-out zipper)
         ;; Basic zipper utilities
         zipper-of/c
         define-struct-zipper-frames
         (contract-out
          [zip (-> any/c zipper?)]
          [zipper-at-top? (-> zipper? boolean?)]
          [zipper-not-at-top? (-> zipper? boolean?)]
          [up (-> zipper-not-at-top? zipper?)]
          [rebuild (-> zipper? any/c)]
          [edit (-> (-> any/c any/c) zipper? zipper?)])
         ;; List zippers
         (struct-out pair-car-frame)
         (struct-out pair-cdr-frame)
         (contract-out
          [down/car (-> (zipper-of/c pair?) zipper?)]
          [down/cdr (-> (zipper-of/c pair?) zipper?)]))

(module+ test
  (require rackunit))

;;;; Zippers

;;; A zipper consists of a context and a focused value. Contexts are
;;; represented as lists of frames, where the empty list is the
;;; context consisting of a hole. Each frame must know how to fill its
;;; hole.

(struct zipper (focus context) #:transparent)

(define (zip obj)
  (zipper obj '()))

;;; Struct frames can be recognized, and we can fill their holes.  The
;;; property should be set to a procedure that, given the frame and a
;;; focus, returns a new focus. We recognize frames with zipper-frame?
(define-values (prop:zipper-frame zipper-frame? zipper-frame-fill)
  (make-struct-type-property 'zipper-frame))


(define (zipper-at-top? z)
  (match z
    [(zipper _ (list))
     #t]
    [_
     #f]))

(define (zipper-not-at-top? z)
  (match z
    [(zipper _ (cons _ _))
     #t]
    [_
     #f]))

(define (zipper-of/c c)
  (make-contract #:name `(zipper-of/c ,c)
                 #:first-order (lambda (z)
                                 (match z
                                   [(zipper focus _)
                                    (c focus)]
                                   [_ #f]))))

;;; To go up, we ask the most recent frame to envelop the focus
(define (up z)
  (match-let* ([(zipper focus (cons frame frames)) z]
               [filler (zipper-frame-fill frame)])
    (zipper (filler frame focus) frames)))

;;; Go up all the way and extract the value
(define (rebuild z)
  (match z
    [(zipper focus (list))
     focus]
    [(zipper _ (cons frame frames))
     (rebuild (up z))]))

;;; Modify the focused value
(define (edit proc z)
  (match z
    [(zipper focus context)
     (zipper (proc focus) context)]))

(define-for-syntax (make-frame-name orig-stx accessor-name)
  (format-id orig-stx "~a-frame" accessor-name #:source orig-stx))

(define-for-syntax (make-down-name orig-stx accessor-name)
  (format-id orig-stx "down/~a" accessor-name #:source orig-stx))

;;; Helper for generating the zipper definitions for a single struct
;;; (see `define-struct-zipper-frames')
(define-for-syntax (generate-zipper-defs orig-stx struct-name)
  (define struct-info
    (extract-struct-info (syntax-local-value struct-name)))

  (define/with-syntax make-name (second struct-info))
  (define/with-syntax name? (third struct-info))
  (define accessors (reverse (fourth struct-info)))
  (define/with-syntax (name-field ...) accessors)
  (define/with-syntax ((frame-struct-name
                        descender-name
                        (fields-pre ...)
                        (fields-pre-patterns ...)
                        (this-field fields-post ...)
                        (fields-post-patterns ...))
                       ...)
    (for/list ([accessor (in-list accessors)]
               [index (in-naturals)])
      (define f-name (make-frame-name orig-stx accessor))
      (define d-name (make-down-name orig-stx accessor))
      (define-values (pre this+post) (split-at accessors index))
      (list f-name d-name pre (generate-temporaries pre) this+post (generate-temporaries (rest this+post)))))
  (syntax/loc orig-stx
    (begin
      (struct frame-struct-name (fields-pre ... fields-post ...)
        #:property prop:zipper-frame
        (lambda (frame focus)
          (match frame
            [(frame-struct-name fields-pre ... fields-post ...)
             (make-name fields-pre ... focus fields-post ...)]))
        #:transparent)
      ...
      (define/contract (descender-name z)
        (-> (zipper-of/c name?) zipper?)
        (match z
          [(zipper (make-name fields-pre-patterns ...
                              new-focus
                              fields-post-patterns ...)
                   context)
           (zipper new-focus (cons (frame-struct-name fields-pre-patterns ... fields-post-patterns ...)
                                   context))]
          [(zipper focus _)
           (raise-argument-error 'descender-name
                                 (symbol->string 'name?)
                                 focus)]))
      ...)))



;;; A macro for deriving zipper frames for structs.
;;;
;;; Essentially, this implements the product rule for the
;;; differentiation underlying zipper derivation.
;;;
;;; For each field in a struct, we generate a new struct representing
;;; the fact that the zipper client descended into that field. This
;;; struct maintains the values of all the other fields, and it's "go
;;; up" procedure reinstantiates them on the correct sides of the
;;; focus. Additionally, each field gets a descend prodecure that, if
;;; the appropriate struct is at the focus of a zipper, will push the
;;; corresponding frame onto the zipper's frame stack and refocus on
;;; that field.
;;;
;;; For a struct (struct s (f1 ... fn)), we generate:
;;;   1. (struct s-f1-frame (f2 ... fn)) ... (struct s-fn-frame (f1 ... fn-1))
;;;      for representing zipper frames
;;;   2. procedures s-f1-down ... s-fn-down for descending the zipper
;;;      into the corresponding field (that is, making s-fk-frame for field fk)
(define-syntax (define-struct-zipper-frames stx)
  (syntax-parse stx
    [(_ name:id names:id ...)
     (quasisyntax/loc stx
       (begin #,(generate-zipper-defs stx #'name)
              #,@(map (lambda (n) (generate-zipper-defs stx n))
                      (syntax->list #'(names ...)))))]))

(define-provide-syntax (struct-zipper-out stx)
  (syntax-parse stx
    [(_ names:id ...)
     (quasisyntax/loc stx
       (combine-out
        #,@(map (lambda (struct-name)
                  (quasisyntax/loc struct-name
                    (combine-out
                     #,@(map (lambda (accessor-name)
                               (quasisyntax/loc struct-name
                                 (combine-out #,(make-frame-name stx accessor-name)
                                              #,(make-down-name stx accessor-name))))
                             (reverse (fourth (extract-struct-info
                                               (syntax-local-value struct-name))))))))
                (syntax->list #'(names ...)))))]))

(module+ test-prov
  (provide (struct-out A)
           (struct-out B)
           (struct-zipper-out A B))
  (struct A (b c d))
  (struct B (b c d))
  (define-struct-zipper-frames A B))

;; TODO
(module test-req racket
  #;
  (require (submod ".." test-prov)))

(module+ test
  ;; TODO
  ;;(require (submod ".." test-prov))

  (struct L () #:transparent)
  (struct T (left right) #:transparent)
  (define-struct-zipper-frames L)       ; no-op
  (define-struct-zipper-frames T)

  (define z1 (zip (T (T (L) (L)) (L))))
  (define z2 (down/T-left z1))
  (check-equal? z2 (zipper (T (L) (L))
                           (list (T-left-frame (L)))))
  (define z3 (up z2))
  (check-equal? z1 z3)
  (define z4 (down/T-right z3))
  (check-equal? z4 (zipper (L) (list (T-right-frame (T (L) (L))))))

  (struct variable (name) #:transparent)
  (struct lam (name body) #:transparent)
  (struct app (rator rand) #:transparent)
  (define-struct-zipper-frames variable lam app)

  (define ω (app (lam "x" (app (variable "x") (variable "x")))
                 (lam "x" (app (variable "x") (variable "x")))))
  (define ω-zipper (zip ω))
  (check-equal? (zipper-at-top? ω-zipper) #t)
  (check-equal? (zipper-not-at-top? ω-zipper) #f)

  (define ω-l (down/app-rator ω-zipper))
  (check-equal?
   ω-l
   (zipper (lam "x" (app (variable "x") (variable "x")))
           (list (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (define ω-l-r (down/lam-body ω-l))
  (check-equal?
   ω-l-r
   (zipper (app (variable "x") (variable "x"))
           (list (lam-body-frame "x")
                 (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (check-equal? (zipper-at-top? ω-l-r) #f)
  (check-equal? (zipper-not-at-top? ω-l-r) #t)

  (check-equal? (up ω-l-r) ω-l)
  (define n (down/variable-name (down/app-rand ω-l-r)))
  (check-equal?
   n
   (zipper "x"
           (list
            (variable-name-frame)
            (app-rand-frame (variable "x"))
            (lam-body-frame "x")
            (app-rator-frame (lam "x" (app (variable "x")
                                           (variable "x")))))))
  (check-equal? (rebuild n) ω)
  )


;;;; Zipper utilities for common datatypes

(struct pair-car-frame (cdr)
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(pair-car-frame x)
       (cons focus x)]))
  #:transparent)

(define (down/car p)
  (match p
    [(zipper (cons fst snd) context)
     (zipper fst (cons (pair-car-frame snd)
                       context))]
    [(zipper focus _)
     (raise-argument-error 'down/car
                           (symbol->string 'pair?)
                           focus)]))

(struct pair-cdr-frame (car)
    #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(pair-cdr-frame x)
       (cons x focus)]))
  #:transparent)

(define (down/cdr p)
  (match p
    [(zipper (cons fst snd) context)
     (zipper snd (cons (pair-cdr-frame fst)
                       context))]
    [(zipper focus _)
     (raise-argument-error 'down/cdr
                           (symbol->string 'pair?)
                           focus)]))


(module+ test
  (define some-list (zip '(a b c d)))
  (define right-twice (down/cdr (down/cdr some-list)))
  (check-equal? right-twice
                (zipper '(c d)
                        (list (pair-cdr-frame 'b)
                              (pair-cdr-frame 'a))))
  (check-equal? (up (down/cdr right-twice)) right-twice)
  (check-equal? (rebuild (edit reverse right-twice))
                '(a b d c))
  (check-eqv? (zipper-focus (down/car right-twice)) 'c)
)

;; |#
