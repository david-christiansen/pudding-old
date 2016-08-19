#lang racket

(require pict presentations zippers
         "presentation-types.rkt"
         "pict-helpers.rkt"
         "sequent-pict.rkt"
         "term-pict.rkt"
         "../proofs.rkt"
         "../infrastructure.rkt")

(provide proof-step/p proof->pict proof-context->pict->pict
         (struct-out with-path))

(define proof-vspace 10)
(define proof-hspace 8)
(define by (text "by" '(bold)))
(define left (text "⟸" '(bold)))

(struct with-path (path proof) #:transparent)


(define (indent-proof-pict p)
  (define indent-space 20)
  (inset p indent-space 0 0 0))

(define/contract (proof-context->pict->pict ctxt canvas [path (list up)])
  (->* ((listof zipper-frame?)
        (is-a?/c presentation-pict-canvas%))
       ((listof zipper-movement?))
      (-> pict-convertible? pict-convertible?))
  (lambda (focus-pict)
    (match ctxt
      [(list)
       focus-pict]
      [(cons prf-frame more)
       (match-define (zipper wrapped new-ctxt)
         (up (zipper focus-pict (cons prf-frame more))))
       ((proof-context->pict->pict new-ctxt canvas (append path (list up)))
        (proof->pict wrapped canvas path))])))

(define/contract (proof->pict step canvas [path '()] #:focus? [focus? #f])
  (->* ((or/c pict-convertible? proof-step?) (is-a?/c presentation-pict-canvas%))
       ((listof zipper-movement?)
        #:focus? boolean?)
       pict-convertible?)
  (define bw (if focus? 3 #f))
  (define (mv n)
    (send canvas make-presentation n metavariable/p
          (thunk* (opaque (text (format "~v" n))))
          hl))
  (define/contract (with-children step pict)
    (-> (or/c with-path? proof-step? pict-convertible?)
        pict-convertible?
        pict-convertible?)
    (match step
      [(with-path path proof)
       (with-children proof pict)]
      [(or (refined-step _ _ _ children _)
           (complete-proof _ _ _ children))
       (apply vl-append proof-vspace pict
              (if (pict-convertible? children)
                  (list (indent-proof-pict children))
                  (for/list ([c children]
                             [i (in-naturals)])
                    (indent-proof-pict
                     (proof->pict c canvas (append path (list (down/proof i))))))))]
      [_ pict]))
  (define/contract (make-step-pict a-step)
    (-> (or/c with-path? proof-step?) pict-convertible?)
    (match a-step
      [(with-path path step)
       (make-step-pict step)]
      [(subgoal name goal)
       (define status (text "?" '(bold)))
       (define n (mv name))
       (define p (inset (hb-append
                         proof-hspace
                         status
                         n
                         left
                         (sequent->pict goal canvas))
                        3))
       (on-box p #:border-width bw)]
      [(irrelevant-subgoal goal)
       (define status (text "?" '(bold)))
       (define p (inset (hb-append
                         proof-hspace
                         status
                         (sequent->pict goal canvas))
                        3))
       (on-box p #:border-width bw)]
      [(refined-step name (>> H G) rule children extractor)
       (define status (text "⤷" '(bold)))
       (define n (mv name))
       (define p
         (inset (hb-append proof-hspace
                           status
                           n
                           left
                           (sequent->pict (>> H G) canvas)
                           (if rule
                               (hb-append proof-hspace
                                          by
                                          (term->pict
                                           (datum->syntax G rule)
                                           canvas
                                           (map hypothesis-name H)))
                               empty))
                3))
       (on-box p #:border-width bw)]
      [(complete-proof (>> H G) rule extract children)
       (define status (text "✔" '(bold)))
       (on-box (inset (hb-append proof-hspace
                                 status
                                 (term->pict extract canvas (map hypothesis-name H))
                                 left
                                 (sequent->pict (>> H G) canvas))
                      3)
               #:border-width bw)]
      [(? pict-convertible? a-pict)
       ;; This is a bit of a hack, but it lets this be easily used
       ;; with the zipper-traversing code
       a-pict]
      [other (on-box (text (format "~v" other)))]))
  (with-children step
    (send canvas make-presentation (with-path path step) proof-step/p
          (lambda (a-step)
            (make-step-pict a-step))
          hl)))
