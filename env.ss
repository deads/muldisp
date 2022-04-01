;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; datatype for environments.
;;
;; Authors: Damian Eads
;;          Jordan Johnson
;;
;; Date:    11/17/2005

(module (empty-env extend-env apply-env
         extend-struct-env fields valid-field-names?
         extend-env-multi)

(import scheme)
(include "match.ss")

(define env-traceables '(empty-env extend-env apply-env extend-struct-env
                                   fields valid-field-names?))

(define (empty-env) '())

;; env sym any -> env
;; Add a binding to an env.
(define (extend-env env var val)
  (cons (cons var val) env))

;; env listof[sym] listof[any] -> env
;; Extend an env with many bindings at once.
(define (extend-env-multi env vars vals)
  (append (map (lambda (var val) (cons var val)) vars vals) env))

(define (apply-env env var)
  (cond
    ((assq var env) => cdr)
    (else #f)))

;;; Data definitions for the structure environment:
;
; A struct-env (or se) is either:
;    (empty-env)
; or (extend-env struct-env sname (sname supname fieldspec ...))
;    where struct-env is the struct-env to extend,
;       sname is the name of the struct type being defined,
;       supname is a symbol that is either a member of struct-env
;                                       or 'Struct
;       and each fieldspec specifies one field of the new struct type.
;
; A fieldspec is a list of the form (type : name) where
;       type is a type (see grammar.ss) indicating the field's type, and
;       name is a symbol representing the name of the field
;
; An extended struct-env also has the property that each field name in a
; struct type's fieldspecs must not occur in any mapping for a supertype of
; that struct type.  e.g., in
;       (extend-env se 'SomeType '(SomeType 'SomeSuper (label0 : T0) ...))
; no label0 may be a name in (fields 'SomeSuper se).
;


; Purpose: extends a struct-env.
;
; Inputs:
;   a-struct-env is the env to extend
;   sname is a symbol, the name of the new type
;   supname is a symbol, the name of the new type's super
;   fieldspec* is a list of fieldspecs for the new type
;
; Returns:
;   A struct-env extended from a-struct-env with a definition of the form
;   (sname supname fieldspec*).
(define (extend-struct-env a-struct-env sname supname fieldspec*)
  (cond
    [(not (andmap pair? fieldspec*))    ;; rudimentary sanity check
     (error 'extend-struct-env "(CH) invalid fieldspec: ~a" fieldspec*)]
    [(eq? supname 'Struct)
     (extend-env a-struct-env sname `(,sname Struct ,fieldspec*))]
    [(not (apply-env a-struct-env supname))
     (error 'extend-struct-env "Unknown supertype: ~a" supname)]
    [(valid-field-names? (map car fieldspec*) supname a-struct-env)
     (extend-env a-struct-env sname `(,sname ,supname ,fieldspec*))]
    [else
     (error 'extend-struct-env
            "invalid subtype: super = <~a>, fields = <~a>"
            supname fieldspec*)]))

;
; Purpose: returns the fields of a valid structure name given
;          an environment.
;
; Inputs:
;   sname is a symbol
;   a-struct-env is a structure environment
;
; Returns:
;   The list of fieldspecs for the structure definition named
;   sname, including the fieldspecs of all the supertypes of
;   sname, ordered from highest to lowest in the type hierarchy.

(define (fields sname a-struct-env)
  (cond
    [(eq? sname 'Struct) '()]
    [(apply-env a-struct-env sname)
       => (lambda (record)
            (match record
              [(,sname ,supname (,fieldspecs ...))
               (append (fields supname a-struct-env)
                       fieldspecs)]
              [,_ (error 'fields "Can't happen: ~a."
                         record)]))
     ]
    [else
     (error 'fields "fields(~a) is not valid." sname)]))

; valid-field-names? : listof[symbol] symbol struct-env -> boolean
; Purpose: return true iff the fields specified in names will not introduce
; a naming conflict with those belonging to supname in the
; environment a-struct-env
;
(define (valid-field-names? names supname a-struct-env)
   ;; Return true iff super doesn't have any field labels that clash with
   ;; those in names.
   (define (no-conflicts? super)
     (or (eq? super 'Struct)
         ;; Check super's fields, then move on:
         (match (apply-env a-struct-env super)
           [(,sup ,next-super ((,labels : ,Ts) ...))
            (and (andmap (lambda (id) (not (memq id labels)))
                         names)
                 (no-conflicts? next-super))])))
   (no-conflicts? supname))

) ;; end module
