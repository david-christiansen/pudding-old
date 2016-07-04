#lang racket

(require pict)

(provide (all-defined-out))

(define/contract (opaque pict)
  (-> pict? pict?)
  (cc-superimpose (filled-rectangle (pict-width pict) (pict-height pict)
                                    #:color "white"
                                    #:draw-border? #f)
                  pict))

;; Highlights
(define/contract (hl pict)
  (-> pict? pict?)
  (let ([w (pict-width pict)]
        [h (pict-height pict)])
    (frame (cc-superimpose
            pict
            (cellophane
             (filled-rectangle w h
                               #:draw-border? #f
                               #:color "yellow")
             0.2))
           #:color "yellow")))


(define (on-box pict #:color [color "white"] #:border-width [border-width #f])
  (cc-superimpose (filled-rectangle (pict-width pict) (pict-height pict) #:color color #:border-width border-width)
                  pict))
