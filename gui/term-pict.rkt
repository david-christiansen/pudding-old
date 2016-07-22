#lang racket
(require pict presentations syntax/parse
         "../expand-bindings.rkt" "../metavariables.rkt"
         "pict-helpers.rkt" "presentation-types.rkt")
(require (prefix-in pp: pprint))
(provide term->pict)

(define (pprint-term stx canvas bindings)
  (-> syntax?
      (is-a?/c presentation-pict-canvas%)
      (listof (cons/c symbol?
                      (or/c (list/c 'bound symbol?)
                            (list/c 'bound #f)
                            (list/c 'free)
                            (list/c 'binding))))
      any/c)
  (syntax-parse stx
    #:literals (lambda)
    [x:id
     (define x-id (get-occurrence-id #'x))
     (define p-type
       (cond [x-id
              (match (assoc x-id bindings)
                [(list _ 'bound binder-id) (binding/p binder-id)]
                [(list _ 'free) free-identifier/p]
                [(list _ 'binding) (binding/p x-id)]
                [#f free-identifier/p])]
             [(list? (identifier-binding #'x))
              free-identifier/p]
             [else unknown-identifier/p]))
     (pp:markup
      (lambda (str)
        (if (string? str)
            (send canvas make-presentation #'x p-type
                  (thunk* (opaque (text str))) hl)
            (send canvas make-presentation #'x p-type
                  (thunk* str) hl)))
      (pp:text (symbol->string (syntax->datum #'x))))]
    [x #:when (metavariable? (syntax-e #'x))
       (pp:markup
        (lambda (str)
          (send canvas make-presentation (syntax-e #'x) metavariable/p
                (thunk* (if (string? str) (opaque (text str)) str))
                hl))
        (pp:text (format "~v" (syntax-e #'x))))]
    #;
    [(lambda (xs:id ...) body)
     (pp:h-append
      pp:lparen
      (pp:v-concat/s
       (list (pp:group
              (pp:hs-append (pprint-term #'lambda canvas)
                            pp:lparen
                            (apply pp:hs-append
                                   (map (lambda (t) (pprint-term t canvas))
                                        (syntax-e #'(xs ...))))
                            pp:rparen))
             (pprint-term #'body canvas)))
      pp:rparen)]
    [(tm ...)
     (pp:markup
      (lambda (p)
        (send canvas make-presentation #'(tm ...) expression/p
              (thunk* p)
              hl))
      (pp:h-append pp:lparen
                   (pp:v-concat/s (map (lambda (t) (pprint-term t canvas bindings))
                                       (syntax-e #'(tm ...))))
                   pp:rparen))]
    [other
     (pp:text (format "~v" (syntax->datum #'other)))]))

(define/contract (term->pict stx canvas bound-identifiers)
  (-> syntax? (is-a?/c presentation-pict-canvas%) (listof identifier?) pict?)
  (define (string->pict x)
    (if (string? x)
        (let ([lines (string-split x "\n" #:trim? #f)])
          (for/fold ([pict (blank)]) ([l lines])
            (vl-append pict (opaque (text l)))))
        x))
  (set! stx (decorate-identifiers stx))
  ;; TODO put expand in the right namespace
  (define bindings (find-bindings (expand stx) bound-identifiers))
  (pp:pretty-markup
   (pprint-term stx canvas bindings)
   (lambda (x y)
     (hb-append (string->pict x) (string->pict y)))
   70))
