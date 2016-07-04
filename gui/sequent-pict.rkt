#lang racket
(require pict presentations
         "../infrastructure.rkt"
         "../expand-bindings.rkt"
         "pict-helpers.rkt"
         "presentation-types.rkt"
         "term-pict.rkt")

(provide sequent->pict hyp->pict)

(define/contract (hyp->pict h canvas prev)
  (-> hypothesis?
      (is-a?/c presentation-pict-canvas%)
      (listof hypothesis?)
      pict?)
  (match h
    [(hypothesis name assumption relevant?)
     (define h-id (get-occurrence-id name))
     (define name-pict
       (send canvas make-presentation name (binding/p h-id)
             (text (format "~a" (syntax-e name)))
             hl))
     (define assumption-pict
       (term->pict assumption canvas (map hypothesis-name prev)))
     (define (wrap p)
       (if relevant?
           p
           (hb-append (text "[") p (text "]"))))
     (wrap (hb-append name-pict (text " : ") assumption-pict))]))

(define/contract (sequent->pict seq canvas)
  (-> sequent? (is-a?/c presentation-pict-canvas%) pict?)
  (match seq
    [(>> H G)
     (define H-pict
       (if (null? H)
           (cc-superimpose
            (ghost (text "()"))
            (filled-ellipse 3 3 #:color "black"))
           (apply hb-append
                  (add-between (reverse
                                (let loop ([hyps H])
                                  (if (null? hyps)
                                      '()
                                      (cons (hyp->pict (car hyps) canvas (cdr hyps))
                                            '() #;(loop (cdr hyps))
                                            ))))
                               (text ", ")))))
     (define G-pict
       (term->pict G canvas (map hypothesis-name H)))
     (hb-append H-pict (text " >> ") G-pict)]))
