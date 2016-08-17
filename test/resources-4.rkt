#lang racket
(require "../resources.rkt" (submod "../resources.rkt" test))
(require (submod "../resources.rkt" test defines-resource))
(require (submod "../resources.rkt" test dark-flavors))
(require (submod "../resources.rkt" test light-flavors))
(require rackunit)
(check-equal? (flavors) '(chocolate devils-food vanilla tapioca))
