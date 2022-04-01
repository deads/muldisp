;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; datatype for evaluation contexts (for use in typechecker)
;;
;; Authors: Damian Eads
;;          Jordan Johnson
;;
;; Date:    10/27/2005

;; Legal types in our system:
;;
;; T ::=        'Bool
;;      |       'Num
;;      |       (T -> T)

;; An type context is either
;;      (empty-context)
;; or   (assume symbol type context)
;;
;; where symbol is a variable name, type is a type to be assumed for the
;; variable, and context is the type context under which the assumption is
;; made.

;; contexts permit this operation:
;;      (type-of symbol context)
;; which returns either the assumed type of the given variable, or #f if there
;; are no assumptions regarding the given variable in the given context.

(module (empty-context assume assume* type-of)

(import scheme)

(define (empty-context) '())

(define (assume var T a-context)
  (cons (cons var T) a-context))

(define (assume* vars Ts a-context)
  (if (null? vars)
      a-context
      (assume (car vars) (car Ts)
              (assume* (cdr vars) (cdr Ts) a-context))))

(define (type-of var a-context)
  (cond
    ((assq var a-context) => cdr)
    (else #f)))

) ;; end module
