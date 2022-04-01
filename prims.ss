;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; Primitive-related functions.
;;
;; Authors: Damian Eads
;;          Jordan Johnson

(module (prim? prim-type)

(import scheme)
(define tprims '(eql le))
(define bprims '(eql and or))
(define aprims '(add mul))
(define prims (append bprims aprims tprims))
(define prim?
  (lambda (x)
    (memq x prims)))

(define prim-type          ;; prim -> type
  (lambda (prim)
    (cond
      [(memq prim tprims)
       '((Int Int) -> Bool)]
      [(memq prim bprims)
       '((Bool Bool) -> Bool)]
      [(memq prim aprims)
       '((Int Int) -> Int)])))

) ;; end module
