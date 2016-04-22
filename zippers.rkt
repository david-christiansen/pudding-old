#lang racket

(require (for-syntax racket/list
                     syntax/parse
                     racket/struct-info
                     racket/syntax))

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
    [(zipper focus (list))
     #t]
    [_
     #f]))

(define (zipper-not-at-top? z)
  (match z
    [(zipper focus (cons _ _))
     #t]
    [_
     #f]))


;;; To go up, we ask the most recent frame to envelop the focus
(define/contract (up z)
  (-> zipper-not-at-top? zipper?)
  (match-let* ([(zipper focus (cons frame frames)) z]
               [filler (zipper-frame-fill frame)])
    (zipper (filler frame focus) frames)))

;;; Go up all the way and extract the value
(define/contract (rebuild z)
  (-> zipper? any/c)
  (match z
    [(zipper focus (list))
     focus]
    [(zipper focus (cons frame frames))
     (rebuild (up z))]))


;;; A massive macro for deriving zipper frames for structs.
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
;;;   2. procedures s-f1-descend ... s-fn-descend for descending the zipper
;;;      into the corresponding field (that is, making s-fk-frame for field fk)
(define-syntax (define-struct-zipper-frames stx)
  (syntax-parse stx
    [(_ struct-name:id)
     (define struct-info
       (extract-struct-info (syntax-local-value #'struct-name)))

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
         (define f-name (format-id stx "~a-frame" accessor #:source stx))
         (define d-name (format-id stx "descend/~a" accessor #:source stx))
         (define-values (pre this+post) (split-at accessors index))
         (list f-name d-name pre (generate-temporaries pre) this+post (generate-temporaries (rest this+post)))))
     #'(begin
         (struct frame-struct-name (fields-pre ... fields-post ...)
           #:property prop:zipper-frame
           (lambda (frame focus)
             (match frame
               [(frame-struct-name fields-pre ... fields-post ...)
                (make-name fields-pre ... focus fields-post ...)]))
           #:transparent)
         ...
         (define (descender-name z)
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
         ...)]
    [(_ name:id names:id ...)
     #'(begin (define-struct-zipper-frames name)
              (define-struct-zipper-frames names) ...)]))


(module+ test
  (struct L () #:transparent)
  (struct T (left right) #:transparent)
  (define-struct-zipper-frames L)       ; no-op
  (define-struct-zipper-frames T)

  (define z1 (zip (T (T (L) (L)) (L))))
  (define z2 (descend/T-left z1))
  (check-equal? z2 (zipper (T (L) (L))
                           (list (T-left-frame (L)))))
  (define z3 (up z2))
  (check-equal? z1 z3)
  (define z4 (descend/T-right z3))
  (check-equal? z4 (zipper (L) (list (T-right-frame (T (L) (L))))))

  (struct variable (name) #:transparent)
  (struct lam (name body) #:transparent)
  (struct app (rator rand) #:transparent)
  ;;(define-struct-zipper-frames var lam app) ;; TODO: make this syntax work
  (define-struct-zipper-frames variable)
  (define-struct-zipper-frames lam)
  (define-struct-zipper-frames app)

  (define ω (app (lam "x" (app (variable "x") (variable "x")))
                 (lam "x" (app (variable "x") (variable "x")))))
  (define ω-zipper (zip ω))
  (check-equal? (zipper-at-top? ω-zipper) #t)
  (check-equal? (zipper-not-at-top? ω-zipper) #f)

  (define ω-l (descend/app-rator ω-zipper))
  (check-equal?
   ω-l
   (zipper (lam "x" (app (variable "x") (variable "x")))
           (list (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (define ω-l-r (descend/lam-body ω-l))
  (check-equal?
   ω-l-r
   (zipper (app (variable "x") (variable "x"))
           (list (lam-body-frame "x")
                 (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (check-equal? (zipper-at-top? ω-l-r) #f)
  (check-equal? (zipper-not-at-top? ω-l-r) #t)

  (check-equal? (up ω-l-r) ω-l)
  (define n (descend/variable-name (descend/app-rand ω-l-r)))
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
