;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; Predicates, info, and conversions between base types and Scheme types:

(module (type:base? bool?
         bool->scheme-bool num->scheme-num
         scheme-bool->bool scheme-num->num)

(import scheme)
(include "match.ss")

(define BASE-TYPES '(Int Bool Datum))

(define (type:base? x)
  (and (memq x BASE-TYPES) #t))

(define (bool? expr) (and (memq expr '(true false)) #t))

(define (bool->scheme-bool p)
  (match p
    [(bool true) #t]
    [(bool false) #f]
    [,_ (error 'bool->scheme-bool "can't happen: ~a" p)]))

(define (scheme-bool->bool p)
  (if p '(bool true) '(bool false)))

(define (num->scheme-num n)
  (match n
    ((num ,i) i)))

(define (scheme-num->num n)
  (if (integer? n)
    `(num ,n)
    (error 'scheme-num->num "attempmted conversion on non-integer: ~a" n)))

) ;; end module
