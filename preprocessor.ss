;; vim:set ai lisp sm mat=2 ft=scheme:
;; File: interpreter.ss
;;
;; Validator/preprocessor for multiple-dispatching language L0.
;;
;; Author: Jordan Johnson
;;
;; Date:    Tue Nov 29 14:59:46 PST 2005

;(case-sensitive #t)


(module preprocessor (preprocess/validate-L0-prog
                      preprocess/validate-L0-defn
                      preprocess/validate-L0-expr)
(import scheme)
(include "match.ss")
(include "basetypes.ss")        ;; for bool?
(include "prims.ss")

;; Data def: An mlist is a list of method names.
;; It is used here to track the methods that are defined, so that an EmptyMM
;; definition can be inserted before each method is joined to a new branch.

;; L0-prog -> L1-prog
;; Convert the L0 program to an equiv. L1, or signal an error if the prog is
;; malformed.
(define (preprocess/validate-L0-prog prog)
  (define (do-prog p)  ;; non-empty list: (defn ... expr) -> L1-prog
    (cond
      [(not (pair? p))
       (error 'preprocess/validate-L0-prog "malformed program: ~a" prog)]
      [(null? (cdr p))
       (list (preprocess/validate-L0-expr (car p)))]
      [else
       (cons (preprocess/validate-L0-defn (car p))
             (do-prog (cdr p)))]))

  ;; L1-prog mlist -> L1-prog
  ;; Takes the validated L1-prog and adds an EmptyMM definition before each
  ;; new method name is defined.
  (define (add-emptymm-defs L1-prog mlist)
    (cond
      [(null? (cdr L1-prog)) L1-prog ]
      [else
       (match (car L1-prog)
         [(def ,methodname : ,T ,e)
          (if (memq methodname mlist)         ;; <- Seen this method yet?
            (cons (car L1-prog)
                  (add-emptymm-defs (cdr L1-prog)
                                    mlist))
            (cons `(def ,methodname EmptyMM)
                  (cons (car L1-prog)
                        (add-emptymm-defs (cdr L1-prog)
                                          (cons methodname mlist)))))]
         [,some-other-def
          (cons (car L1-prog)
                (add-emptymm-defs (cdr L1-prog)
                                  mlist))])]))

  (cond
    [(null? prog) (error 'preprocess/validate-L0-prog
                         "No program given.")]
    [else (add-emptymm-defs (do-prog prog) '())]))


;; L0-defn -> L1-defn
;; Convert the L0 defn to an equiv. L1, or signal an error if the defn is
;; malformed.
(define preprocess/validate-L0-defn
  (let ()
    ;; Normalize struct defns by removing 'extends', giving explicit
    ;; supertypes to all, and wrapping fspecs:
    (define (preproc-sdef d)
      (match d
        [(def-struct ,S extends ,T ,fields)
         (cond
           [(not (symbol? S))
            (error 'preprocess/validate-L0-defn
                   "bad structure type name: ~a" S)]
           [(not (symbol? T))
            (error 'preprocess/validate-L0-defn
                   "bad supertype name: ~a" T)]
           [else
            `(def-struct ,S ,T ,(validate/convert-fspec-list fields))])]
        [(def-struct ,S ,fields)
         (cond
           [(not (symbol? S))
            (error 'preprocess/validate-L0-defn
                   "bad structure type name: ~a" S)]
           [else
            `(def-struct ,S Struct ,(validate/convert-fspec-list fields))])]
        [,_ (error 'preprocess/validate-L0-defn
                   "invalid struct definition: ~a"
                   d)]))

    ;; Validate method definitions and convert to var defns:
    (define (preproc-mdef d)
      (match d
        [(defm (,f . ,fmls) : ,T ,body)
         (cond
           [(not (symbol? f))
            (error 'preprocess/validate-L0-defn
                   "bad method name: ~a" f)]
           [(not (has-type-structure? T))
            (error 'preprocess/validate-L0-defn
                   "invalid method return type: ~a" T)]
           [(null? fmls)
            (error 'preprocess/validate-L0-defn
                   "method has no args: ~a" f)]
           [else
            (let* ((fmls (validate/convert-fspec-list fmls))
                   ;; Extract fml types:
                   (S* (map caddr fmls)))
              `(def ,f : (,S* -> ,T)
                 (join (var ,f)
                       (lambda ,fmls ,(preprocess/validate-L0-expr body)))))])]
        [,_ (error 'preprocess/validate-L0-defn
                   "malformed method definition: ~a" d)]))

    ;; Validate var definitions and convert to var defns:
    (define (preproc-def d)
      (match d
        [(def ,x ,e)
         (if (not (symbol? x))
           (error 'preprocess/validate-L0-defn
                  "bad variable name in def: ~a" x)
           `(def ,x ,(preprocess/validate-L0-expr e)))]
        [,_ (error 'preprocess/validate-L0-defn
                   "malformed var definition: ~a" d)]))

    ;; Body of preprocess/validate-L0-defn:
    (lambda (defn)
      (cond
        [(not (pair? defn))
         (error 'preprocess/validate-L0-defn
                "malformed definition: ~a" defn)]
        [(not (memq (car defn) '(def-struct defm def)))
         (error 'preprocess/validate-L0-defn
                "malformed definition: ~a" defn)]
        [else (case (car defn)
                ((def-struct)   (preproc-sdef defn))
                ((defm)         (preproc-mdef defn))
                ((def)          (preproc-def defn)))]))))


;; L0-expr -> L1-expr
;; Convert the L0 expr to an equiv. L1, or signal an error if the expr is
;; malformed.
(define (preprocess/validate-L0-expr e)
  (match e
    [,n (guard (integer? n))    `(num ,n)]
    [,p (guard (bool? p))       `(bool ,p)]
    [EmptyMM 'EmptyMM]
    [,x (guard (symbol? x))     `(var ,x)]
    [(if ,[e0] ,[e1] ,[e2])     `(if ,e0 ,e1 ,e2)]
    [(if . ,x)
     (error 'preprocess/validate-L0-expr "malformed if-expr: ~a" `(if . ,x))]
    [(lambda ,fmls ,[body])
     (if (null? fmls)
       (error 'preprocess/validate-L0-expr "zero-arg lambda: ~a"
              `(lambda ,fmls ,body))
       (let ((fmls (validate/convert-fspec-list fmls)))
         `(lambda ,fmls ,body)))]
    [(lambda . ,x)
     (error 'preprocess/validate-L0-expr "malformed lambda: ~a"
            `(lambda . ,x))]
    [(join ,[e0] ,[e1])         `(join ,e0 ,e1)]
    [(join . ,x)
     (error 'preprocess/validate-L0-expr "malformed join: ~a" `(join . ,x))]
    [(,prim ,[e0] ,[e1])                ;;; XXX binary prims only
     (guard (prim? prim))
     `(primapp ,prim ,e0 ,e1)]
    [(,prim . ,x)
     (guard (prim? prim))
     (error 'preprocess/validate-L0-expr "malformed primapp: ~a"
            `(,prim . ,x))]
    [(,[e0] => ,[e1] ,[e2] ...) `(,e0 => ,e1 ,e2 ...)]
    [(=> . ,x)
     (error 'preprocess/validate-L0-expr "malformed dispatch: ~a"
            `(=> . ,x))]
    [(,any => . ,x)
     (error 'preprocess/validate-L0-expr "malformed dispatch: ~a"
            `(,any => . ,x))]
    [(of ,[e0] ,label)
     (if (symbol? label)
       `(of ,e0 ,label)
       (error 'preprocess/validate-L0-expr "bad field accessor: ~a" label))]
    [(of . ,x)
     (error 'preprocess/validate-L0-expr "malformed struct access: ~a"
            `(of . ,x))]
    [(new ,T ,[arg] ...)
     (if (has-type-structure? T)
       `(new ,T ,arg ...)
       (error 'preprocess/validate-L0-expr
              "invalid type in constructor: ~a" T))]
    [(new . ,x)
     (error 'preprocess/validate-L0-expr "malformed constructor: ~a"
            `(new . ,x))]
    [(as ,T ,[e0])
     (if (has-type-structure? T)
       `(as ,T ,e0)
       (error 'preprocess/validate-L0-expr
              "invalid type in cast: ~a" T))]
    [(as . ,x)
     (error 'preprocess/validate-L0-expr "malformed cast: ~a"
            `(as . ,x))]
    [(,[e0] ,[e1] ,[e2] ...)    `(app ,e0 ,e1 ,e2 ...)]
    [,e
     (error 'preprocess/validate-L0-expr
            "malformed expression: ~a"
            e)]))



;;; Helper code:

;; validate/convert-fspec-list : list -> listof[L1-fspec]
;; Takes a list of the form
;;      (sym0 : type0 ...)
;; and wraps each sym:type pair in parens.  The list may be null, so the null
;; case must be checked separately when this is used for lambda formals.
(define validate/convert-fspec-list
  (let ()
    (define (check/wrap-pair id T)
      (cond
        [(not (symbol? id))
         (error 'validate/convert-fspec-list "invalid id: ~a" id)]
        [(not (has-type-structure? T))
         (error 'validate/convert-fspec-list
                "field/formal id ~a has invalid type: ~a" id T)]
        [else `(,id : ,T)]))
    (lambda (fls)
      (match fls
        [() '()]
        [(,x : ,T . ,[rest])
         (cons (check/wrap-pair x T) rest)]
        [,_ (error 'validate/convert-fspec-list
                   "invalid formals/fields list: ~a" fls)]))))

;; any -> bool
;; true iff x is structured like a legit function type (see grammar.ss).
(define (has-fn-type-structure? x)
  (match x
    [((,T ...) -> ,U)
     (and (andmap has-type-structure? T)
          (has-type-structure? U))]
    [,_ #f]))

;; any -> bool
;; true iff x is structured like a legit type.
(define (has-type-structure? x)
  (or (symbol? x)
      (has-fn-type-structure? x)
      (match x
        [(method ,fntype ...)
         (andmap has-fn-type-structure? fntypes)]
        [,_ #f])))

;;;;; Test code: ;;;;;

(include "test.ss")

;; Tests for add-emptymm-defs:
;; (remember to bring it out to toplevel if you're testing again!)
;(tatf (test:list
;        (add-emptymm-defs '((def f : ((Int) -> Int) blahblah)
;                            (def f : ((Datum) -> Datum) blah)
;                            some-expr)
;                          '())
;          -- '((def f EmptyMM)
;               (def f : ((Int) -> Int) blahblah)
;               (def f : ((Datum) -> Datum) blah)
;               some-expr)
;        (add-emptymm-defs '((def f : ((Int) -> Int) blahblah)
;                            (def f : ((Datum) -> Datum) blah)
;                            (def g : ((Car) -> Driver) blahfoo)
;                            some-expr)
;                          '())
;          -- '((def f EmptyMM)
;               (def f : ((Int) -> Int) blahblah)
;               (def f : ((Datum) -> Datum) blah)
;               (def g EmptyMM)
;               (def g : ((Car) -> Driver) blahfoo)
;               some-expr)
;        (add-emptymm-defs '(some-lone-expr) '())
;          -- '(some-lone-expr)
;          ))

;; Tests for validate/convert-fspec-list:
;(tatf (test:list
;        (validate/convert-fspec-list '())
;          -- '()
;        (validate/convert-fspec-list 'a)
;          -- "<error>.*invalid.*"
;        (validate/convert-fspec-list '(x bogus Int))
;          -- "<error>.*invalid.*"
;        (validate/convert-fspec-list '(5 : 23))
;          -- "<error>.*invalid id: 5"
;        (validate/convert-fspec-list '(x : 23))
;          -- "<error>.*invalid type: 23"
;        (validate/convert-fspec-list '(x : Int y : Bool z : Car))
;          -- '((x : Int) (y : Bool) (z : Car))
;        (validate/convert-fspec-list '(x : ((Int) -> Int)
;                                       y : ((Car Bool) -> Vehicle)))
;          -- '((x : ((Int) -> Int))
;               (y : ((Car Bool) -> Vehicle)))
;          ))

) ;; end module
