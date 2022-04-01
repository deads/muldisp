;; vim:set ai lisp sm mat=2 ft=scheme:
;; Author: Jordan Johnson <jmj@soe.ucsc.edu>
;;
;; Typing and subtyping-related functions.


(module typing-subtyping (variable? type? types-equal?
                          type:function? type:struct-name? type:method?
                          <: Struct<: arglist<:)

(import scheme)
(include "match.ss")
(include "env.ss")
(include "basetypes.ss")

;;;; Type type predicates and accessors.

(define variable? symbol?)


(define (type? x se)
  (or (type:base? x)
      (type:function? x se)
      (type:struct-name? x se)
      (type:method? x se)))

;; function-type -> listof[type]
;; Given a function type, return its list of formal arg types.
(define type:domain
  (lambda (spec) ;; assertion needed here later, (type:function? spec)
    (match spec
      [(,in -> ,out) in]
      [,_ (error 'type:domain "can't happen")])))

;; function-type -> type
;; Given a function type, return its output type.
(define type:range
  (lambda (spec)
    (match spec
      [(,in -> ,out) out]
      [,_ (error 'type:range "can't happen")])))

;; types-equal? : type type env -> boolean
;; tells whether two given types are equal, under the given type environment.
(define types-equal?
  (lambda (type1 type2 se)
    (cond
      [(and (type:base? type1) (type:base? type2))
       (eq? type1 type2)]
      [(and (type:struct-name? type1 se) (type:struct-name? type2 se))
       (eq? type1 type2)]
        ;; If type1 and type2 are both function types, their domains and ranges
        ;; must be equal.
      [(and (type:function? type1 se) (type:function? type2 se))
       (and (andmap (lambda (t1 t2) (types-equal? t1 t2 se))
                    (type:domain type1)
                    (type:domain type2))
            (types-equal? (type:range type1) (type:range type2) se))]
      [(and (type:method? type1 se) (type:method? type2 se))
       (let ((fntypes1 (match type1 [(method ,fntypes ...) fntypes]))
             (fntypes2 (match type2 [(method ,fntypes ...) fntypes])))
         (and (= (length fntypes1) (length fntypes2))
              (andmap (lambda (t1 t2) (types-equal? t1 t2 se))
                      fntypes1
                      fntypes2)))]
      [else #f])))


;; Is the type specification passed a function.
;;
;; Pre:
;;  x: is a type specification
;;
;; Post:
;;  true if x is a type specification for a function;
;;  false, otherwise.
;;
;; Examples:
;; (type:function? '((Bool) -> Bool)) -> #t
;; (type:function? '((((Bool) -> Int)) -> Bool)) -> #t

;; ((((PV1) PV2) PV3) PV4)

;; PVI=((x1 : T1) (x : T2) ...) body env

(define type:function?
  (lambda (x se)
    (match x
      [((,t0 ,t1 ...) -> ,u)
       (and (type? t0 se)
            (andmap (lambda (y) (type? y se))
                    t1)
            (type? u se))]
      [,_ #f])))

(define type:struct-name?
  (lambda (x se)
    (and (symbol? x)
         (or (eq? x 'Struct)
             (and (apply-env se x) #t)))))

(define type:method?
  (lambda (x se)
    (match x
      [(method ,ft ...)
      ;; Note, we only check that the ft's are a listof[functiontype]; we
      ;; don't check the other necessary invariants (cf. Castagna et al.).
       (andmap (lambda (y)
                 (type:function? y se))
               ft)]
      [,_ #f])))

;; type type env -> boolean
;; true iff S is a subtype of T.
(define (<: S T se)
  (or (eq? T 'Datum)
      (types-equal? S T se)
      (and (type:struct-name? S se)
           (type:struct-name? T se)
           (Struct<: S T se))
      (and (type:function? S se) (type:function? T se) (function<: S T se))
      (and (type:method? S se) (type:method? T se) (method<: S T se))
      (and (list? S) (list? T)
           (arglist<: S T se))))

;; symbol symbol env -> boolean
;; true iff S is a subtype of T, where S,T are struct type identifiers
(define (Struct<: S T se)
  (define (<:T S)
    (and (not (eq? S 'Struct))
         (or (eq? S T)
             (let ((s-record (apply-env se S)))
               (match s-record
                 [(,S1 ,superS ,fields ...)
                  (<:T superS)]
                 [#f (error '<:T "Unknown structure type name:  <~a>" S)]
                 [,_ (error '<:T "can't happen: failed match on ~a"
                            s-record)])))))
  (or (eq? T 'Struct)
      (<:T S)))

;; type type env -> boolean
;; true iff F1 is a subtype of F2, where F1,F2 are function types
(define (function<: F1 F2 se)
  (match F1
    [(,S1 -> ,T1)
     (match F2
       [(,S2 -> ,T2)
        (and (arglist<: S2 S1 se)
             (<: T1 T2 se))]
       [,_ (error 'function<: "can't happen: function<: got a bad F2")])]
    [,_ (error 'function<: "can't happen: function<: got a bad F1")]))

;; listof[type] listof[type] env -> boolean
;; true iff S* is a subtype of T*, where S*,T* are lists of types
(define (arglist<: S* T* se)
  (and (pair? S*)
       (pair? T*)
       (= (length S*) (length T*))
       (andmap (lambda (s t) (<: s t se)) S* T*)))

;; type type env -> boolean
;; true iff M1 is a subtype of M2, where M1,M2 are method types.
;; M1 <: M2 iff (M2's member function types comprise a subset of M1's types,
;;               or every function type in M2 is subtyped by one in M1)
(define (method<: M1 M2 se)
  (define (fntype-subset? f1t* f2t*)   ;; is f1t* a subset of f2t*?
    (andmap (lambda (f1t)
              (exists (lambda (f2t) (types-equal? f1t f2t se))
                      f2t*))
            f1t*))

  (define (depth-subtype? f1t* f2t*)
    ;; true iff every elt of f2t* has a corresponding subtype function in
    ;; f1t*.
    (andmap (lambda (f2t)
              (not (null? (filter (lambda (f1t) (function<: f1t f2t se))
                                  f1t*))))
            f2t*))
  (match M1
    ((method ,f1types ...)
     (match M2
       ((method ,f2types ...)
        (or (fntype-subset? f2types f1types)
            (depth-subtype? f1types f2types)))
       (,_ (error 'method<:
                  "can't happen: method<: received non-method-type M2."))))
    (,_ (error 'method<:
               "can't happen: method<: received non-method-type M1."))))


;;;;; Generic helpers: ;;;;;

;; ('a -> boolean) 'a list -> boolean
;; true iff ls contains some member x for which (pred? x) is true.
(define (exists pred? ls)
  (and (not (null? ls))
       (or (pred? (car ls))
           (exists pred? (cdr ls)))))

;(define playse
;  (extend-env
;    (extend-env
;      (extend-env (empty-env)
;                  'Vehicle '(Vehicle Struct (velocity : Int) (weight : Int)))
;      'Car '(Car Vehicle (stereo? : Bool)))
;    'Animal '(Animal Struct (size : Int))))
;
;(define playse2
;  (extend-env
;   (extend-env
;    (extend-env playse 'Mazda '(Mazda Car (factoryBuilt : Int)))
;    'Miata '(Miata Mazda))     ;; no fields added
;   'Human '(Human Animal (ride : Car))))
;
;; Some of these refer to testing defns in typecheck.ss...
;(define subtyping-tests
;  (test:list
;   (function<: f3t f5t playse) -- #f
;   (function<: f5t f3t playse) -- #t
;
;   (Struct<: 'Vehicle 'Car playse2) -- #f
;   (Struct<: 'Car 'Vehicle playse2) -- #t
;   (Struct<: 'Mazda 'Vehicle playse2) -- #t
;   (Struct<: 'Miata 'Vehicle playse2) -- #t
;   (Struct<: 'Car 'Animal playse2) -- #f
;   (Struct<: 'Animal 'Car playse2) -- #f
;   (Struct<: 'Bogus 'Car playse2)
;     -- "<error> <:T: Unknown structure type name:  <Bogus>"
;
;   (arglist<: '() '() playse2) -- #f
;   (arglist<: '(Vehicle) '(Vehicle) playse2) -- #t
;   (arglist<: '(Car) '(Vehicle) playse2) -- #t
;   (arglist<: '(Vehicle Car) '(Vehicle Car) playse2) -- #t
;   (arglist<: '(Vehicle Car) '(Vehicle Mazda) playse2) -- #f
;   (arglist<: '(Vehicle Mazda) '(Vehicle Car) playse2) -- #t
;   (arglist<: '(Vehicle Mazda Animal) '(Car Mazda Car) playse2) -- #f
;   (arglist<: '(Vehicle Mazda Animal) '(Car Mazda) playse2) -- #f
;   (arglist<: '(Vehicle Mazda Animal) '(Struct Car Animal) playse2) -- #t
;   (arglist<: '(Vehicle Mazda Animal) '(Struct Struct Struct) playse2) -- #t
;
;   (map (lambda (x)
;          (Struct<: x 'Struct playse2))
;        '(Vehicle Car Mazda Miata Animal Struct)) -- '(#t #t #t #t #t #t)
;        ))

;(define subtype-rels '(Struct<: <: function<: arglist<: method<:))

) ;; end module
