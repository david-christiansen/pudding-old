;; Set up indentation for a couple macros here
((racket-mode .
              ((eval . (put 'let! 'racket-indent-function 1))
               (eval . (put 'match-let! 'racket-indent-function 1))
               (eval . (put 'match! 'racket-indent-function 1)))))
