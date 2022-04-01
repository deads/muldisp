;; vim:set ai lisp sm mat=2 ft=scheme:
;; File: interpreter.ss
;;
;; multiple-dispatching language's interpreter.
;;
;; Authors: Damian Eads
;;          Jordan Johnson
;;
;; Date:    11/17/2005

;(case-sensitive #t)

(module interpreter (eval-L2-prog eval-L2-defn eval-L2-expr)

(import scheme)
(include "env.ss")
(include "basetypes.ss")
(include "match.ss")
(include "typing-subtyping.ss")
(import typing-subtyping)

;;;;; The interpreter: ;;;;;

;; L2-prog env struct-env env -> L2-value
(define (eval-L2-prog p env se me)
  (cond
    [(null? (cdr p))
     (eval-L2-expr (car p) env se me)]
    [else
     (let-values ([(env se me) (eval-L2-defn (car p) env se me)])
       (eval-L2-prog (cdr p) env se me))]))


;; L2-defn env struct-env env -> env struct-env env
;; Eval a definition and extend the appropriate env.
(define (eval-L2-defn defn env se me)
  (match defn
    ((def-struct ,stype ,supertype (,fspecs ...))
     (values env
             (extend-struct-env se stype supertype fspecs)
             me))
    ((def ,x ,e)
     (let ((v (eval-L2-expr e env se me)))
       (if (eq? v 'EmptyMM)                     ;; method defn.
         (values env
                 se
                 (extend-env me x v))
         (values (extend-env env x v)           ;; normal var defn.
                 se
                 me))))
    ((def ,f : ,T ,e)
     (values env
             se
             (extend-env me f (eval-L2-expr e env se me))))))

;; L2-expr -> L2-val
;; Evaluate an expression.
(define (eval-L2-expr expr env se me)
  (match expr
    ;; value types:
    ((num ,n) `(num ,n))
    ((bool ,p) `(bool ,p))
    ((procval ((,x : ,T) ...) ,U ,e ,env)
     (error 'eval-L2-expr "attempted to eval a procval: ~a"
            `(procval ((,x : ,T) ...) ,e ,env)))
    ((struct ,T ,superT ,v ...)
     (error 'eval-L2-expr "attempted to eval a struct val: ~a"
            `(struct ,T ,superT ,v ...)))
    ((method ((,x : ,T) ,U ,e ,env) ...)
     (error 'eval-L2-expr "attempted to eval a method val: ~a"
            `(method ((,x : ,T) ,e ,env) ...)))
    (EmptyMM 'EmptyMM)
    ;; expr types:
    ((if ,[tst] ,e0 ,e1)
     (eval-L2-expr (if (bool->scheme-bool tst) e0 e1)
                   env se me))
    ((var ,x)
     (or (apply-env env x)
         (apply-env me x)
         (error 'eval-L2-expr "(CH) unbound variable: ~s" x)))
    ((lambda ,fspecs ,rtype ,body)
     `(procval ,fspecs ,rtype ,body ,env))     ;; create a closure
    ((join ,[v0] ,[v1])
     (merge-bodies v0 v1 se))
    ((app ,[proc] ,[rands] ...)
     (match proc
       [(procval ((,fmls : ,Ts) ...) ,U ,body ,closure-env)
        (eval-L2-expr body
                      (extend-env-multi closure-env fmls rands)
                      se
                      me)]
       [,_ (error 'eval-L2-expr "attempted to apply non-proc <~a>" proc)]))
    ((,[m] => ,[args] ...)
     (dispatch m args se me))
    ((of ,[sval] ,id)
     (struct-ref sval id se))
    ((new ,X ,[args] ...)
     (make-struct X args se))
    ((primapp ,prim ,[args] ...)
     (apply-prim prim args))
    ((as ,T ,[val])
     ;; val must actually be of type T (or a subtype) for the cast to work:
     (let ((S (runtime-type-of val se)))
       (if (<: S T se)
         val
         (error 'eval-L2-expr "failed cast: ~a (type <~a>) to ~a" val S T))))
    (,_ (error 'eval-L2-expr "(CH) invalid expr: ~a" _))))

;;;;; Method-related helpers ;;;;;

;; method-val procval -> method-val
;; Insert the function body in the appropriate place.
(define (merge-bodies meth pval se)
  (define (input-types fn)        ;; extract fml types of given fn skeleton.
    (match fn
      [(((,x : ,T) ...) ,U ,body ,env) T]
      [,_ (error 'input-types "can't happen: match on ~a" fn)]))

  (let* ((pv-body (cdr pval))
         (pv-types (input-types pv-body)))
    (define (insert-body meth-bodies)
      (cond
        ((null? meth-bodies) (list pv-body))
        ((arglist<: pv-types (input-types (car meth-bodies)) se)
         (cons pv-body meth-bodies))
        (else (cons (car meth-bodies)
                    (insert-body (cdr meth-bodies))))))
    (match meth
      [EmptyMM `(method ,pv-body)]
      [(method . ,bodies)
       `(method . ,(insert-body bodies))]
      [,_ (error 'merge-bodies "(CH) invalid method val: ~a" meth)])))

;; dispatch : method-val listof[L2-value] struct-env env -> L2-value
;; Select the appropriate branch of the given method and apply it to the given
;; args.
(define (dispatch meth args se me)
  ;; In the following 2 functions, cbody is a method/procval body without the
  ;; method/procval tag in the car. (Like "bodies" in merge-bodies above.)

  ;; Return true iff cbody can accept the given args (ie, args are of subtype
  ;; of fmls):
  (define (ok-for-dispatch? cbody)
    (match cbody
      [(((,fmls : ,Ts) ...) ,U ,body ,env)
       (and (= (length fmls) (length args))
            (arglist<: (map (lambda (val) (runtime-type-of val se)) args)
                       Ts se))]
      [,_ (error 'dispatch "bogus procval: ~a" `(procval . ,cbody))]))

  ;; Apply the given closure body to the args
  (define (invoke cbody)
    (match cbody
      [(((,fmls : ,Ts) ...) ,U ,body ,env)
       (eval-L2-expr body (extend-env-multi env fmls args) se me)]
      [,_ (error 'dispatch "bogus procval: ~a" `(procval . ,cbody))]))

  ;; Choose an appropriate method branch for the given args
  ;; (there should be such a branch) and apply it to them.
  (define (choose-branch bodies)
    (cond
      ((null? bodies)
       (error 'dispatch "no branch matching args: ~a" args))
      ((ok-for-dispatch? (car bodies))
       (invoke (car bodies)))
      (else (choose-branch (cdr bodies)))))
  (match meth
    [EmptyMM (error 'dispatch "EmptyMM - no branch matching args: ~a" args)]
    [(method . ,bodies) (choose-branch bodies)]
    [,_ (error 'dispatch "bogus method: ~a" meth)]))

;;;;; Struct-related helpers ;;;;;

;; struct-ref : struct-val sym struct-env -> L2-val
;; Returns the given struct's field named by id.
(define (struct-ref sval id se)
  (match sval
    [(struct ,stype ,super ,field-vals)
     (let ((field-names (map car (fields stype se))))
       ;; Return the value for the field that matches id:
       (or (ormap (lambda (fname fval) (and (eq? fname id) fval))
                  field-names field-vals)
           (error 'struct-ref "can't happen: bad struct-ref: ~a->~a"
                  stype id)))]
    [,_ (error 'struct-ref "bogus struct: ~a" sval)]))

;; make-struct : sym listof[L2-val] struct-env -> struct-val
;; Creates the appropriate struct-val.
(define (make-struct stype field-args se)
  (match (apply-env se stype)
    [(,sname ,supname . ,fields)
     `(struct ,sname ,supname ,field-args)]
    [#f (error 'make-struct "can't happen: unknown s-type ~a" stype)]))

;;;;; Primitives: ;;;;;

;; apply-prim : prim listof[L2-val] -> L2-val
;; Returns the result of the given primitive operation.
(define (apply-prim prim args)
  (case prim
    ((eql le add mul)
     (let ((n1 (num->scheme-num (car args)))
           (n2 (num->scheme-num (cadr args))))
       (case prim
         ((eql) (scheme-bool->bool (= n1 n2)))
         ((le)  (scheme-bool->bool (<= n1 n2)))
         ((add) (scheme-num->num (+ n1 n2)))
         ((mul) (scheme-num->num (* n1 n2))))))
    ((and or)
     (let ((p1 (bool->scheme-bool (car args)))
           (p2 (bool->scheme-bool (cadr args))))
       (if (eq? prim 'and)
         (scheme-bool->bool (and p1 p2))
         (scheme-bool->bool (or p1 p2)))))))

;;;;; Runtime typechecks: ;;;;;

;; This function is required for runtime cast checking and method dispatching.

;; L1-val struct-env -> L1-type
;; Returns the known type of a value, for use at runtime in the interpreter.
(define (runtime-type-of L1-val se)
  (match L1-val
    [(num ,n) 'Int]
    [(bool ,p) 'Bool]
    [(procval ((,fmls : ,Ts) ...) ,U ,body ,env)
     `((,Ts ...) -> ,U)]
    [(struct ,stype ,supertype ,fspecs)
     stype]
    [(method (((,x : ,T) ...) ,U ,body ,env) ...)
     `(method ((,T ...) -> ,U) ...)]
    [EmptyMM '(method)]))


;;;;; Test code: ;;;;;

(include "test.ss")

;; Tests for runtime-type-of:
;(tatf (test:list
;        (runtime-type-of '(num 5) '()) -- 'Int
;        (runtime-type-of '(bool true) '()) -- 'Bool
;        (runtime-type-of '(bool false) '()) -- 'Bool
;        (runtime-type-of '(procval ((x : Int) (y : Int) (huh? : Bool)) Struct
;                            (if (var huh?) (new Struct) (new Struct))
;                            '())
;                         (empty-env))
;          -- '((Int Int Bool) -> Struct)
;        (runtime-type-of 'EmptyMM (empty-env)) -- '(method)
;        (runtime-type-of '(method
;                            (((x : Int) (y : Bool)) Car
;                                (new Car (var x) (var x) (var y))
;                                '())
;                            (((x : Int) (y : Int)) Vehicle
;                                (new Vehicle (var x) (var x))
;                                '()))
;                         (empty-env))
;          -- '(method ((Int Bool) -> Car) ((Int Int) -> Vehicle))
;        ))


;; expr env val -> test-pair
;; Creates a test-pair mapping (eval-exp e env) to val.
(define (test-eval-L2-expr e env val)
  (fn-test val e eval-L2-expr e env '() '()))  ; and se and me

;; this function translates the test format below (my original attempt) to the
;; test format used in test.ss. --jmj, 11/17/05
(define (convert-tests e-tests)
  (map (lambda (tx) (apply test-eval-L2-expr tx))
       e-tests))

;;;; Specific test cases follow:

(define expr-tests
  (convert-tests
  `(((num 25) ,(empty-env) (num 25))
    ((num 10) ,(empty-env) (num 10))
    ((var x) ,(empty-env) ".*unbound var.*")
    ((app (lambda ((x : Int)) Int (var x)) (num 4)) ,(empty-env) (num 4))
    ((app (lambda ((x : Bool)) Bool (var x)) (bool true))
     ,(empty-env)
     (bool true))
    ((app (lambda ((x : Bool)) Bool (var x)) (bool false))
     ,(empty-env)
     (bool false))
    ((app (lambda ((x : Int)) Int (primapp mul (var x) (var x))) (num 4))
     ,(empty-env)
     (num 16))
    ((app (lambda ((x : Int)) Int (primapp mul (var x) (var x))) (num 4))
     ,(empty-env)
     (num 16))
    ((lambda ((m : Int)) Int
       (lambda ((x : Int)) Int
         (lambda ((b : Int)) Int
           (primapp add (var b) (primapp mul (var m) (var x))))))
     ,(empty-env)
     (procval ((m : Int)) Int
       (lambda ((x : Int)) Int
         (lambda ((b : Int)) Int
           (primapp add (var b) (primapp mul (var m) (var x)))))
       ()))
    ((app (app (app (lambda ((m : Int)) Int
                      (lambda ((x : Int)) Int
                        (lambda ((b : Int)) Int
                          (primapp add (var b) (primapp mul (var m) (var x))))))
                    (num 10))
               (num 3))
          (num 4))
     ,(empty-env)
     (num 34))
    ((primapp add (num 5) (num 20)) ,(empty-env) (num 25))
    ((primapp add (num 0) (num 20)) ,(empty-env) (num 20))
    ((primapp eql (num 3) (num 10)) ,(empty-env) (bool false))
    ((primapp eql (num 10) (num 3)) ,(empty-env) (bool false))
    ((primapp eql (num 10) (num 10)) ,(empty-env) (bool true))
    ((primapp or (bool true) (bool true)) ,(empty-env) (bool true))
    ((primapp or (bool true) (bool false)) ,(empty-env) (bool true))
    ((primapp or (bool false) (bool true)) ,(empty-env) (bool true))
    ((primapp or (bool false) (bool false)) ,(empty-env) (bool false))
    ((primapp and (bool true) (bool true)) ,(empty-env) (bool true))
    ((primapp and (bool true) (bool false)) ,(empty-env) (bool false))
    ((primapp and (bool false) (bool true)) ,(empty-env) (bool false))
    ((primapp and (bool false) (bool false)) ,(empty-env) (bool false))
    ((primapp mul (num 3) (num 11)) ,(empty-env) (num 33))
    ((primapp mul (num 0) (num 10)) ,(empty-env) (num 0))
    ((primapp mul (num 1) (num 10)) ,(empty-env) (num 10))
    ((if (bool true) (num 1) (num 0)) ,(empty-env) (num 1))
    ((if (bool false) (num 1) (num 0)) ,(empty-env) (num 0))
    ((if (primapp eql (num 10) (num 100))
       (primapp add (num 1) (num 1))
       (primapp add (num 2) (num 2)))
     ,(empty-env)
     (num 4))
    ((if (primapp eql
                  (primapp mul (num 3) (num 5))
                  (primapp add (num 14) (num 1)))
       (primapp add (num 3) (num 9))
       (primapp add (num 2) (num 8)))
     ,(empty-env)
     (num 12))
    )))

(define terp-traceables
  '(apply eval-L2-prog eval-L2-defn eval-L2-expr merge-bodies dispatch
                 struct-ref make-struct test-eval-L2-expr apply-prim))

(define (go!)
  (testall expr-tests terp-traceables))

; (eval `(trace ,@terp-traceables))

) ;; end module
