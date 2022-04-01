;; vim:set ai lisp sm mat=2 ft=scheme:
;


(module (find-first filter)

(import scheme)

; Finds the first element of the list that passes the predicate, #f if
; none found.
;
; Inputs:
;   ok? : Any unary predicate
;   ls : A list of elements that the predicate can accept.
(define (find-first ok? ls)
  (and (not (null? ls))
       (let ((first (car ls)))
         (or (and (ok? first) first)
             (find-first ok? (cdr ls))))))

(define (filter ok? ls)
  (cond
    ((null? ls) '())
    ((ok? (car ls))
     (cons (car ls) (filter ok? (cdr ls))))
    (else
      (filter ok? (cdr ls)))))

) ;; end module
