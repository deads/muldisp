;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; Grammar for the language, sexp-style.

;; This file defines two grammars:
;;      L0      is the input language entered by users
;;      L1      is the intermediate language that is interpreted
;;
;; Overview of the implementation:
;;
;;      User -> L0 -> preprocess/validate -> L1 -> check -> eval -> L1-val
;;
;; Ellipsis notation denotes zero or more of the item preceding the ellipsis
;; (as in Scheme macros).

(define L0-grammar
  '(forms (prog (defn ... expr))
          (defn (def-struct sym (sym0 : type0           ;; extends Struct
                                 sym1 : type1
                                 ...))
                (def-struct sym extends sym (sym0 : type0
                                             sym1 : type1
                                             ...))
                (defm (sym sym0 : type0
                           sym1 : type1
                           ...) : type
                  expr)
                (def sym expr))
          (expr n                               ;; num (int)
                p                               ;; bool
                sym                             ;; var
                EmptyMM
                (if expr expr expr)
                (lambda (sym0 : type0
                         sym1 : type1
                         ...) expr)
                (join expr expr)
                (expr => expr expr ...)
                (prim expr expr ...)
                (of expr sym)
                (new sym expr ...)
                (as sym expr)
                (expr expr expr ...)
                )
          (type Num Bool Datum
                sym                            ;; struct name
                ((type type ...) -> type)
                (method ((type type ...) -> type) ...))
          (prim eql le and or add mul)))

;; L1: output from preprocessor/validator, input for typechecker.

(define L1-grammar
  '(forms (prog (defn ... expr))
          (defn (def-struct sym sym (fspec ...))        ;; struct def
                (def sym expr)                          ;; var def
                (def sym : type expr))                  ;; method def
          (expr (num n)
                (bool p)
                (var sym)
                EmptyMM
                (if expr expr expr)
                (lambda (fspec fspec ...) expr)
                (join expr expr)
                (app expr expr expr ...)
                (expr => expr ...)
                (primapp prim expr ...)
                (of expr sym)
                (new sym expr ...)
                (as sym expr))          ;; cast to struct/base type
          (type Num Bool Datum
                sym                            ;; struct name
                ((type type ...) -> type)
                (method ((type type ...) -> type) ...))
          ;               ^ arg1's type     ^outtype^ more function types
          (fspec (sym : type))
          (prim eql le and or add mul)))

;; L2: output from typechecker, input for interpreter.
;; Same as L1, except lambdas are type-tagged and values are added.

(define L2-grammar
  '(forms (prog (defn ... expr))
          (defn (def-struct sym sym (fspec ...))        ;; struct def
                (def sym expr)                          ;; var def
                (def sym : type expr))                  ;; method def
          (expr value
                (var sym)
                (if expr expr expr)
                (lambda (fspec fspec ...) type expr)    ;; CHANGED from L1
                (join expr expr)
                (app expr expr expr ...)
                (expr => expr ...)
                (primapp prim expr ...)
                (of expr sym)
                (new sym expr ...)
                (as sym expr))          ;; cast to struct/base type
          (value (num n)
                 (bool p)
                 ;; procval CHANGED from L1:
                 (procval (fspec fspec ...) type expr env)
                 (struct sym sym value ...)
                 ;; method CHANGED from L1:
                 (method ((fspec fspec ...) type expr env) ...)
                 EmptyMM)
          (type Num Bool Datum
                sym                            ;; struct name
                ((type type ...) -> type)
                (method ((type type ...) -> type) ...))
          ;               ^ arg1's type     ^outtype^ more function types
          (fspec (sym : type))
          (prim eql le and or add mul)))

;;; Templates for functions on the grammar:
;; L0:
(define (process-L0-prog p etc)
  (cond
    [(null? (cdr p))
     (process-L0-expr (car p) etc)]
    [else ... (process-L0-defn (car p) etc)
          ... (process-L0-prog (cdr p) etc) ... ]))

(define (process-L0-defn defn etc)
  (match defn
    ((def-struct ,stype ,fields)
     ... (flist->fspecs fields) ...)
    ((def-struct ,stype extends ,supertype ,fields)
     ... (flist->fspecs fields) ...)
    ((defm (,f . ,fmls) : ,T ,e)
     ... (flist->fspecs fmls)
     ... (process-L0-expr e etc) ...)
    ((def ,x ,e)
     ... (process-L0-expr e etc) ...)
    ))

;; list -> listof[fspec]
;; Takes a list of the form (sym : type sym : type ...) and wraps each
;;      sym : type
;; grouping in parens.
(define (flist->fspecs fields)
  (cond
    ((null? fields) '())
    ((or (null? (cdr fields)) (null? (cddr fields)))
     (error 'flist->fspecs "malformed field list: ~a" fields))
    (else (let ((label (car fields))
                (colon (cadr fields))
                (type (caddr fields))
                (rest (cdddr fields)))
            (cond
              ((not (eq? colon ':))
               (error 'flist->fspecs "malformed field list: ~a" fields))
              (else (cons `(,label : ,type) (flist->fspecs rest))))))))

(define (process-L0-expr e etc)
  (match e
    (,n
     (guard (integer? n))
     ...)
    (,p
     (guard (bool? p))
     ...)
    (,x
     (guard (symbol? x))
     ...)
    (EmptyMM
      ...)
    ((if ,[tst] ,[then] ,[else])
     ...)
    ((lambda ,fmls ,body)
     ... (flist->fspecs fmls)
     ... (process-L0-expr body ...) ...)
    ((join ,[m] ,[fn])
     ...)
    ((,[m] => ,[arg0] ,[arg1] ...)
     ...)
    ((,prim ,[arg0] ,[arg1] ...)
     (guard (prim? prim))
     ...)
    ((of ,[s] ,field)
     ...)
    ((new ,stype ,[arg] ...)
     ...)
    ((as ,type ,[expr])
     ...)
    ((,[proc] ,[arg0] ,[arg1] ...)
     ...)))

;; L2:

(define (process-L2-prog p etc)
  (cond
    [(null? (cdr p))
     (process-L2-expr (car p) etc)]
    [else ... (process-L2-defn (car p) etc)
          ... (process-L2-prog (cdr p) etc) ... ]))

(define (process-L2-defn defn etc)
  (match defn
    ((def-struct ,stype ,supertype (,fspec ...))
     ...)
    ((def ,x ,e)
     ... (process-L2-expr e etc) ...)
    ((def ,f : ,T ,e)
     ... (process-L2-expr e etc) ...)))

(define (process-L2-expr expr etc)
  (match expr
    ;; value types:
    ((num ,n)
      ...)
    ((bool ,p)
      ...)
    ((procval ((,x : ,T) ...) ,U ,e ,env)
     ...)
    ((struct ,T ,superT ,v ...)
     ...)
    ((method ((,x : ,T) ,U ,e ,env) ...)
     ...)
    (EmptyMM
      ...)
    ;; expr types:
    ((if ,[tst] ,[e0] ,[e1])
     ...)
    ((var ,var) (guard (variable? var))
      ...)
    ((lambda ((,var : ,T) ...) ,U ,body)
     (process-L2-expr body etc))
    ((join ,[e0] ,[e1])
     ...)
    ((app ,[e0] ,[e1] ...)
     ...)
    ((,[e0] => ,[e1] ...)
     ...)
    ((of ,[e] ,id)
     ...)
    ((new ,X ,[e] ...)
     ...)
    ((primapp ,prim ,[e0] ,[e1])
     ...)
    ((as ,T ,[e])
     ...)
    ))
