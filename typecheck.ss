;; vim:set ai lisp sm mat=2 ft=scheme:
;;
;; Authors: Damian Eads <eads@soe.ucsc.edu>
;;          Jordan Johnson <jmj@soe.ucsc.edu>
;;
;; Type checker for the language defined in grammar.ss.
;;

;(case-sensitive #t)

(module typecheck (check-L1-prog check-L1-defn check-L1-expr)

(import scheme)
(include "match.ss")
(include "env.ss")
(include "context.ss")
(include "helpers.ss")
(include "prims.ss")
(include "basetypes.ss")

(include "typing-subtyping.ss")
(import typing-subtyping)


;; Notational cue:  if you see capital T in a var name here, think "type."

;; check-L1-prog : L1-prog -> L2-prog
;; EFFECT: prints types as they are determined.
(define (check-L1-prog p)
  (let loop ((p p)
             (context (empty-context))
             (se (empty-env)))
    (cond
      [(null? (cdr p))
       (let-values ([(expr T) (check-L1-expr (car p) context se)])
         (list expr))]
      [else
       (let-values ([(defn T context se) (check-L1-defn (car p) context se)])
         ;; For feedback, print the name being def'd, and its type:
         (printf "# ~a : ~a~n" (cadr defn) T)
         (cons defn (loop (cdr p) context se)))])))


;; check-L1-defn : L1-defn context struct-env
;;                      -> (values L2-defn type context struct-env)
;; Typecheck a definition.   The returned context
;; or struct-env are possibly-extended versions of those given. The type
;; returned will be the type of the value being defined.
(define (check-L1-defn d context se)

  ;; OK, here's the ugliness:
  ;; We have to fool the typechecker into taking
  ;;    (join f (lambda (...) ... f ...))
  ;; where f has some known method type in the context but will have a
  ;; different type after this definition (including in the lambda body).
  ;; So the ref to f in the lambda should have a different assumed type than
  ;; the f in the LHS of the join.
  ;;
  ;; The hack is to extract the type of the LHS variable, use it to typecheck
  ;; the join manually, and then return a join of the original LHS with the
  ;; new join-RHS.
  ;;
  ;; Yep, it's ugly.  Seems to me when we introduced a separate method env,
  ;; that suggests we should have a separate method var type context--but then
  ;; we'd have to distinguish varrefs.  This business of higher-order methods
  ;; is silly.
  ;;
  ;; sym type expr[join] context struct-env
  ;;    -> (values expr[join] type context se)
  (define (check-toplevel-join x xT def-rhs context se)
    (match def-rhs
      [(join (var ,y) ,join-rhs)
       (guard (eq? x y))                ;; <-- important -- and always true!
       (let ((old-yT (type-of y context)))
         (cond
           [(not old-yT)
            (error 'check-L1-defn "(CH) defm: join of unknown method type")]
           [else
            (match old-yT
              [(method . ,x-funtypes)
               (let* ((mtype (extend-method-type x-funtypes xT se))
                      (context (assume x mtype context)))
                 (let-values ([(new-join-rhs join-rhsT)
                               (check-L1-expr join-rhs context se)])
                   (cond
                     [(not (type:function? join-rhsT se))
                      (error 'check-L1-defn
                             "(CH) defm: toplevel join with non-fn type: ~a"
                             join-rhsT)]
                     [(not (types-equal? xT join-rhsT se))
                      (error 'check-L1-defn
                             "defm: ~a : ~a does not match user-def'd type ~a"
                             x join-rhsT xT)]
                     [else
                      (values `(def ,x : ,xT
                                 (join (var ,y) ,new-join-rhs))
                              mtype
                              context
                              se)])))]
              [,_ (error 'check-L1-defn
                         "(CH) defm: toplevel join on non-method type ~a"
                         old-yT)])]))]
      [,_ (error 'check-L1-defn "(CH) messed up defm translation: ~a"
                 `(def ,x : ,xT ,def-rhs))]))

  (match d
    [(def-struct ,S ,T ((,labels : ,fieldTs) ...))
     (cond
       [(not (andmap (lambda (fT) (type? fT se)) fieldTs))
        (error 'check-L1-defn "ill-typed field in struct def: ~a" d)]
       [(apply-env se S)
          => (lambda (S-rec)
               (error 'check-L1-defn "redefinition of type ~a" S))]
       [else
        (values d       ;; safe since no match-recursion is used here.
                S
                context
                (extend-struct-env se S T
                                   `((,labels : ,fieldTs) ...)))])]
    [(def ,x ,e)
     (when (type-of x context)
       (error 'check-L1-defn "redefinition of variable ~a" x))
     (let-values ([(L2-e L2-T) (check-L1-expr e context se)])
       (values `(def ,x ,L2-e)
               L2-T
               (assume x L2-T context)
               se))]
    [(def ,x : ,T ,e)           ;; method defn
     (if (type? T se)
       (check-toplevel-join x T e context se)   ;; 4 ret vals.
       (error 'check-L1-defn "(CH) invalid type in defm: ~a" T))]))


;; check-L1-expr : L1-expr context struct-env -> (values L2-expr type)
;; Return
;;      a tagged version of the given expression (made by tagging lambdas with
;; return types)
;;      the type of the given expression under the assumptions of the given
;; context if the expression is well-typed.
;;
;; Signal an error if the L1-expr is ill-typed.
(define (check-L1-expr expr context se)
  (match expr
    ;; value types:
    ((num ,n) (guard (integer? n))
      (values `(num ,n) 'Int))
    ((bool ,p) (guard (bool? p))
      (values `(bool ,p) 'Bool))
    [(method (,formals ,body ,env) ...)
     (error 'check-L1-expr "method is not an input form of the language.")]
    [EmptyMM
     (values 'EmptyMM '(method))]
    ;; non-value forms follow.
    ;; ,[foo] means to recur and bind the result to foo
    [(if ,[tst tst-T] ,[e0 e0-T] ,[e1 e1-T])
     (cond
       ((not (eq? tst-T 'Bool))
        (error 'check-L1-expr
              "ill-typed if-expr: ~a~%\tNon-boolean test."
              expr))
       ((not (types-equal? e0-T e1-T se))
        (error 'check-L1-expr
               "ill-typed if-expression: ~a~%\tThen: <~a> vs. Else: <~a>"
               expr e0-T e1-T))
       (else (values `(if ,tst ,e0 ,e1) e0-T)))]    ;; well-typed if-expr.
    [(var ,var)
     (guard (variable? var))
     (let ((T (type-of var context)))
       (cond
         ((not T)
          (error 'check-L1-expr "unbound variable: ~a" var))
         (else (values `(var ,var) T))))]
    [(lambda ((,var : ,T) ...) ,body)
     (if (andmap (lambda (Tn) (type? Tn se)) T)
         (let-values ([(body outputType)
                       (check-L1-expr body (assume* var T context) se)])
           (values `(lambda ((,var : ,T) ...) ,outputType ,body)
                   `(,T -> ,outputType)))
         (error 'check-L1-expr "unknown type in formals list ~a" T))]
    [(join ,[e0 e0t] ,[e1 e1t])
     (cond
       [(not (type:method? e0t se))
        (error 'check-L1-expr "Attempted to join non-method ~a" e0t)]
       [(not (type:function? e1t se))
        (error 'check-L1-expr "Attempted to join method type ~a with non-function ~a"
               e0t e1t)]
       [else
        (match e0t
          [(method ,funtypes ...)
           (values `(join ,e0 ,e1)
                   (extend-method-type funtypes e1t se))]
          [,_ (error 'check-L1-expr "can't happen: bad join")])])]
    [(app ,[e0 e0t] ,[actuals actualTs] ...)
     (pretty-print `(app ,e0 ,actuals))
     (cond
       [(type:function? e0t se)
        (match e0t
          [((,fmlTs ...) -> ,S)
           ;; Must have req'd number of args:
           (cond
             [(not (= (length fmlTs) (length actualTs)))
              (error 'check-L1-expr
                     "incorrect number of arguments for function app in ~a"
                     expr)]
             [(andmap (lambda (fmlT actualT)   ;; Apply subsumption rule:
                        (<: actualT fmlT se))
                      fmlTs
                      actualTs)
              ;; Now we know all the input types are OK, so the result is...
              (values `(app ,e0 ,actuals ...) S)]
             [else
              (error 'check-L1-expr
                     "Attempt to apply funtype ~a to actual types ~a"
                     e0t actualTs)])]
          [,_ (error 'check-L1-expr "can't happen: bad app")])]
       [else
        (error 'check-L1-expr "Attempt to apply non-function: ~a" e0t)])]
    [(,[meth mT] => ,[args arglistT] ...)
     ;; Find any appropriate fn type in the method for the given args:
;     (printf "dispatch on ~a~n" arglistT)
     (let ((ftype
            (match mT
              [(method ,funtypes ...)
               (find-first (lambda (mft)
;                             (printf "mft: ~a~n" mft)
                             (match mft
                               [(,S -> ,T) (arglist<: arglistT S se)]
                               [,_
                                (error 'check-L1-expr
                                   "can't happen: malformed method type.")]))
                           funtypes)]
              [,_
               (error 'check-L1-expr
                      "attempt to dispatch on non-method type ~a." mT)])))
       (match ftype
         [(,S -> ,T)                                    ;; ...got one!
          (values `(,meth => ,args ...) T)]
         [#f (error 'check-L1-expr
                    "no type found for dispatch in ~a"
                    `(,meth => ,args ...))]
         [,_ (error 'check-L1-expr
                    "can't happen: bad return value from find-first")]))]
    [(of ,[struct-expr sT] ,id)
     (guard (symbol? id))
     (if (type:struct-name? sT se)
         (let ((fs* (fields sT se)))    ;; see env.ss for fields defn.
           (cond
             [(assq id fs*) =>
               (lambda (fspec)
                 (values `(of ,struct-expr ,id) (caddr fspec)))]
             [else (error 'check-L1-expr
                          "~a is not a valid field name for struct type ~a"
                          id sT)]))
         (error 'check-L1-expr
                "Attempted to access field ~a of non-structure type ~a."
                id sT))]
    [(new ,X ,[args argTs] ...)
     (if (type:struct-name? X se)
         (let ((X-fieldTs (fields X se)))
           ;; each arg type in argTs must be a subtype of its corresponding
           ;; field type in X:
           (cond
             [(not (= (length argTs) (length X-fieldTs)))
              (error 'check-L1-expr
                     "Incorrect number of fields in constructor: ~a"
                     `(new ,X ,argTs))]
             [(andmap (lambda (fspec actual-type)
                         (match fspec
                           ;; XXX yuck, depends on fspec structure:
                           [(,label : ,field-type)
                            (<: actual-type field-type se)]
                           [,_
                            (error 'check-L1-expr
                                   "can't happen: bad field spec ~a"
                                   fspec)]))
                       X-fieldTs argTs)
               (values `(new ,X ,args ...) X)]          ;;; <-- RESULT.
             [else
               (error 'check-L1-expr
                      "Constructor for ~a requires ~a, received ~a"
                      X X-fieldTs argTs)]))
         (error 'check-L1-expr "Constructing a non-structure type ~a" X))]
     [(primapp ,prim ,[e0 e0t] ,[e1 e1t])       ;; XXX yucko, what if we
      (guard (prim? prim))                      ;; have non-binary prims?
      (let ((ptype (prim-type prim)))
        (match ptype
          [((,t0 ,t1) -> ,r)
           (cond
             [(not (types-equal? e0t t0 se))
              (error 'check-L1-expr
                     "first argument to ~a is of type ~a; should be ~a."
                     prim e0t t0)]
             [(not (types-equal? e1t t1 se))
              (error 'check-L1-expr
                     "second argument to ~a is of type ~a; should be ~a."
                     prim e1t t1)]
             [else
              (values `(primapp ,prim ,e0 ,e1) r)])]    ;;; <-- RESULT.
          [,_ (error 'check-L1-expr "can't happen: bad app")]))
     ]
    [(as ,T ,[e eT])
     (guard (type? T se))
     (cond 
       [(<: eT T se)                    ; up-cast
        (values `(as ,T ,e) T)]
       [(<: T eT se)                    ; down-cast
        (values `(as ,T ,e) T)]
       [else                            ; stupid-cast
        (printf "*** Warning: casting ~a to ~a may be considered 'stupid'...\n"
                eT T)
        ;; ...then trust the programmer anyway (oyy, will we ever learn?):
        (values `(as ,T ,e) T)])]
    [,_
     (error 'check-L1-expr "malformed/invalid input program: ~a" expr)]))

; Purpose: Checks the validity of a function inserted into an
;          existing method.
; Inputs:
;  mfts : list of function types belonging to the existing method
;  ft : the function type to insert into the method
;
; Returns:
;   If valid, it returns the new method type, otherwise, an error
;   is signaled.

(define (extend-method-type mfts ft se)
  (let ((S (car ft))
        (T (caddr ft)))         ; ft is S -> T
    (define (ok? mfts)
      (or (null? mfts)
          (and (match (car mfts)
                 [(,U -> ,V)
                  (case (compare-argtype-lists S U se)
                    [(unrelated) #t]
                    [(subtype) (<: T V se)]
                    [(supertype) (<: V T se)]
                    [(equal)
                     (error 'extend-method-type
                            "function type ~a is already in method ~a"
                            ft mfts)]
                    [(ambiguous)
                     (error 'extend-method-type
                            "ambiguous method join.")])]
                 [,_ (error 'extend-method-type "can't happen")])
               (ok? (cdr mfts)))))
    (and (ok? mfts) (cons 'method (cons ft mfts)))))

; Data definition: A rel is a symbol describing the relationship of
; two parameter type lists A and B. It is either:
;
;   * unrelated : if A and B are of unequal length or they contain
;   unrelated arguments at a specific position.
;
;   * subtype : if A is a subtype of B.
;
;   * supertype : if B is a subtype of A.
;
;   * equal : if A and B are the same type.
;
;   * ambiguous : if there are two argument positions with opposite
;   subtyping relations.
;
; Types other than parameter type lists can also be described by
; any rel other than 'ambiguous.

;
; Purpose: Determines the relationship between two argument list types.
; This relationship is defined in terms of a rel.
;
; Inputs:
;   A and B are argument type lists (A1 A2 ...) and (B1 B2 ...)
;   se is a structure environment

(define (compare-argtype-lists A* B* se)
  (define (classify-argtype A B)
    (cond
      [(types-equal? A B se) 'equal]
      [(<: A B se) 'subtype]
      [(<: B A se) 'supertype]
      [else 'unrelated]))
  (define (classify-argtype-lists A B known-rel)
    (cond
      [(and (null? A) (null? B)) known-rel]
      [(or (null? A) (null? B)) 'unrelated] ; unequal length
      [else
       (let ((A1 (car A))
             (B1 (car B)))
         (case (classify-argtype A1 B1)
           [(equal) (classify-argtype-lists (cdr A) (cdr B) known-rel)]
           [(subtype)
            (case known-rel
              [(equal subtype)
               (classify-argtype-lists (cdr A) (cdr B) 'subtype)]
              [(supertype) 'ambiguous]
              [(unrelated)
               (error 'compare-argtype-lists "Cannot happen, subtype.")])]
           [(supertype)
            (case known-rel
              [(equal supertype)
               (classify-argtype-lists (cdr A) (cdr B) 'supertype)]
              [(subtype) 'ambiguous]
              [(unrelated)
               (error 'compare-argtype-lists "Cannot happen, supertype.")])]
           [(unrelated)
             'unrelated]))]))
  (let* ((A1 (car A*))
         (B1 (car B*))
         (rel (classify-argtype A1 B1)))
    (case rel
      [(unrelated) 'unrelated]
      [else
       (classify-argtype-lists (cdr A*) (cdr B*) rel)])))


;;;;; Testing code: ;;;;;

;(include "test.ss")

;; just-check-type : L1-expr context structenv -> type
;; Typecheck, but return only the expr type (and not the re-tagged expr).
;(define (just-check-type expr context se)
;  (let-values ([(new-expr T) (check-L1-expr expr context se)])
;    T))

; Struct is the supertype of all types.
; XXX use extend-struct-env instead!
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
;(define f1t '((Int) -> Int))
;(define f2t '((Int Bool) -> Bool))
;(define f3t '((Car Int) -> Bool))
;(define f4t '((Animal ((Animal) -> Bool)) -> Bool))
;
;(define f5t '((Vehicle Int) -> Bool))                   ;; note f5t <: f3t
;
;(define f6t '((Vehicle Animal) -> Bool))                   ;; note f5t <: f3t
;
;(define f7t '((Car Animal) -> Bool))
;
;;(define f8t '((Car Struct) -> Bool))                ;; note type conflict
;                                                    ;; f6t and f8t -- glb is
;                                                    ;; not one of the two
;                                                    ;; types.
;(define f9t '((Struct Struct) -> Bool))
;
;(define f10 '((Vehicle Car) -> Bool))               ;; note type conflict
;(define f11 '((Car Struct) -> Bool))                ;; f6t and f8t
;
;(define m1t '(method))
;(define m2t `(method ,f1t ,f2t))
;(define m3t `(method ,f6t ,f3t))
;
;(define m4t `(method ,f5t ,f7t))




;(define type-pred-tests
;  (test:list
;   (map (lambda (t) (type:function? t playse)) (list f1t f2t f3t f4t f5t))
;   -- (make-list 5 #t)
;   (type:function? m2t playse) -- #f
;   (type:function? '((Bool) -> Bool) playse) -- #t
;   (type:function? '((((Bool) -> Int)) -> Bool) playse) -- #t
;   (map (lambda (t) (type:method? t playse)) (list m1t m2t m3t m4t))
;   -- '(#t #t #t #t)
;
;   (types-equal? '((Int) -> Int) '((Int) -> Int) '()) -- #t
;   (type:method? f3t playse) -- #f
;   (type:method? 'Struct playse2) -- #f
;   (type:method? 'Car playse2) -- #f
;   (type:method? 'Int playse2) -- #f
;   (type:method? '(Vehicle Mazda Animal) playse2) -- #f
;   (type:method? '() playse2) -- #f
;
;   (type:struct-name? f1t playse) -- #f
;   (type:struct-name? m1t playse) -- #f
;   (type:struct-name? m2t playse) -- #f
;   (type:struct-name? 'Bool playse) -- #f
;   (type:struct-name? 'Struct playse) -- #t
;   (type:struct-name? 'Car playse) -- #t
;   (type:struct-name? 'Vehicle playse) -- #t
;
;   )) ;; end type predicate tests

 ;; end subtyping tests

;; Test lambdas in the language:
;(define id '(lambda ((x : Datum)) (var x)))
;
;(define struct-5 '(lambda ((s : Struct)) (num 5)))        ;; test subsumption
;
;(define veh-wt '(lambda ((v : Vehicle)) (of (var v) weight)))
;
;(define fn1 '(lambda ((m : Int) (x : Int) (b : Int))
;               (primapp add (var b) (primapp mul (var m) (var x)))))
;
;(define typecheck-tests
;  (let ()
;    (define ec (empty-context))
;    (define (ck e)
;      (just-check-type e ec playse2))
;    (test:list
;      (ck '(num 5)) -- 'Int
;      (ck '(num 3.5))
;        -- "<error> check-L1-expr: malformed/invalid input program: (num 3.5)"
;      (ck '(bool true)) -- 'Bool
;      (ck '(bool false)) -- 'Bool
;      (ck `(procval ((n : Int) (m : Int)) (primapp add m n) ,(empty-env)))
;         -- "^<error>.*"
;      (ck '(struct Car Vehicle (num 120) (num 1800) (bool false)))
;         -- "^<error>.*"
;      (ck `(method (((n : Int)) (var n) ,(empty-env))
;                   (((b : Bool)) (var b) ,(empty-env))))
;         -- "^<error>.*"
;
;      (ck 'EmptyMM) -- '(method)
;      (ck '(if (bool true) (num 5) (num 4))) -- 'Int
;      (ck '(if (bool false) (bool false) (num 4)))
;         -- "<error> check-L1-expr: ill-typed if-expression: (if (bool false) (bool false) (num 4))\n\tThen: <Bool> vs. Else: <Int>"
;
;      (ck '(var 5))
;         -- "^<error>.*"
;      (ck '(var x))
;         -- "<error> check-L1-expr: unbound variable: x"
;
;      (ck id) -- '((Datum) -> Datum)
;      (ck '(lambda ((x : Int)) (var x))) -- '((Int) -> Int)
;      (ck '(lambda ((x : Int))
;             (lambda ((x : Bool))
;               (var x))))
;        -- '((Int) -> ((Bool) -> Bool))
;      (ck '(lambda ((x : Int) (y : Int))
;             (lambda ((b : Bool))
;               (if (var b) (var x) (var y)))))
;        -- '((Int Int) -> ((Bool) -> Int))
;      (ck '(lambda ((m : Int) (x : Int) (b : Int))
;             (primapp add (var b) (primapp mul (var m) (var x)))))
;        -- '((Int Int Int) -> Int)
;      (ck '(lambda ((f : ((Int) -> Int)))
;             (primapp and (app (var f) (num 3)) (bool true))))
;        -- "<error> check-L1-expr: first argument to and is of type Int; should be Bool."
;
;      (ck '(lambda ((x : Blargh)) (var x)))
;        -- "<error> check-L1-expr: unknown type in formals list (Blargh)" ;; undefined fml type
;
;      (ck '(lambda ((f : ((Hippo) -> Hippo)))
;             (var f)))
;        -- "<error> check-L1-expr: unknown type in formals list (((Hippo) -> Hippo))" ;; undefined fml type
;
;      ;; Apps w/subsumption:
;      (ck `(app ,id (num 6))) -- 'Datum
;      (ck `(app ,id (bool false))) -- 'Datum
;      (ck `(app ,id (new Struct))) -- 'Datum
;      (ck `(app ,id ,id)) -- 'Datum
;
;      (ck `(app ,struct-5 (new Struct))) -- 'Int
;      (ck `(app ,struct-5 (new Car (num 100) (num 1000) (bool true)))) -- 'Int
;      (ck `(app ,veh-wt
;                (new Car (num 100) (num 1000) (bool false))))
;        -- 'Int
;      (ck `(app ,veh-wt
;                (new Miata (num 55) (num 1800) (bool true) (num 3))))
;        -- 'Int
;      (ck `(app ,veh-wt (new Struct)))
;        -- "<error> check-L1-expr: Attempt to apply funtype ((Vehicle) -> Int) to actual types (Struct)"
;
;      (ck '(app (lambda ((f : ((Int) -> Struct)))
;                  (app (var f) (num 100)))
;                (lambda ((n : Int))
;                  (new Car
;                       (primapp mul (var n) (num 4))
;                       (primapp mul (var n) (num 15))
;                       (bool true)))))
;        -- 'Struct
;
;      (ck '(new Hippo))
;        -- "<error> check-L1-expr: Constructing a non-structure type Hippo"
;      (ck '(new Struct)) -- 'Struct
;      (ck '(of (new Car (num 100) (num 1000) (bool false)) weight)) -- 'Int
;      (ck '(of (new Struct) weight))
;        -- "<error> check-L1-expr: weight is not a valid field name for struct type Struct"
;      (ck '(of (num 5) weight))
;        -- "<error> check-L1-expr: Attempted to access field weight of non-structure type Int."
;      (ck '(of (lambda ((x : Int)) (var x)) weight))
;        -- "<error> check-L1-expr: Attempted to access field weight of non-structure type ((Int) -> Int)."
;      (ck '(of (new Human
;                    (num 10) ; size (from Animal)
;                    (new Car (num 100) (num 1000) (bool false))) ride))
;        -- 'Car
;      (ck '(of (new Human
;                    (new Car (num 100) (num 1000) (bool false))) ride))
;        -- "<error> check-L1-expr: Incorrect number of fields in constructor: (new Human (Car))"
;
;      (ck '(primapp mul (num 3) (num 5))) -- 'Int
;      (ck '(primapp mul (num 5) (bool true)))
;        -- "<error> check-L1-expr: second argument to mul is of type Bool; should be Int."
;      (ck '(primapp mul (bool true) (bool true)))
;        -- "<error> check-L1-expr: first argument to mul is of type Bool; should be Int."
;      
;      (ck '(primapp add (num 3) (num 5))) -- 'Int
;      (ck '(primapp add (num 5) (bool true)))
;        -- "<error> check-L1-expr: second argument to add is of type Bool; should be Int."
;      (ck '(primapp add (bool true) (bool true)))
;        -- "<error> check-L1-expr: first argument to add is of type Bool; should be Int."
;      (ck '(primapp add (primapp mul (num 3) (num 7)) (num 2)))
;        -- 'Int
;
;      (ck '(primapp eql (num 3) (primapp add (num 5) (num 6)))) -- 'Bool
;      (ck '(primapp eql (bool true) (bool false)))
;        -- "<error> check-L1-expr: first argument to eql is of type Bool; should be Int."
;      (ck '(primapp eql (new Struct) (new Struct)))
;        -- "<error> check-L1-expr: first argument to eql is of type Struct; should be Int."
;      (ck '(primapp eql
;                    (new Car (num 100) (num 1000) (bool true))
;                    (new Vehicle (num 100) (num 1000))))
;        -- "<error> check-L1-expr: first argument to eql is of type Car; should be Int."
;
;      (ck '(primapp le (num 3) (primapp add (num 5) (num 6)))) -- 'Bool
;      (ck '(primapp le (bool true) (bool false)))
;        -- "<error> check-L1-expr: first argument to le is of type Bool; should be Int."
;      (ck '(primapp le (new Struct) (new Struct)))
;        -- "<error> check-L1-expr: first argument to le is of type Struct; should be Int."
;      (ck '(primapp le (new Car (num 100) (num 1000) (bool false))
;                (new Vehicle (num 100) (num 1250))))
;        -- "<error> check-L1-expr: first argument to le is of type Car; should be Int."
;
;      (ck '(primapp and (num 3) (primapp add (num 5) (num 6))))
;        -- "<error> check-L1-expr: first argument to and is of type Int; should be Bool."
;      (ck '(primapp and (bool true) (bool false))) -- 'Bool
;      (ck '(primapp and (bool true) (primapp and (bool true) (bool false)))) -- 'Bool
;      (ck '(primapp and (new Struct) (new Struct)))
;        -- "<error> check-L1-expr: first argument to and is of type Struct; should be Bool."
;      (ck '(primapp and (new Car (num 100) (num 1000) (bool false))
;                (new Vehicle (num 100) (num 125))))
;        -- "<error> check-L1-expr: first argument to and is of type Car; should be Bool."
;
;      (ck '(primapp and (new Car (num 100) (num 1000))
;                (new Vehicle (num 100))))
;        -- "<error> check-L1-expr: Incorrect number of fields in constructor: (new Vehicle (Int))"
;
;      (ck '(primapp or (num 3) (primapp add (num 5) (num 6))))
;        -- "<error> check-L1-expr: first argument to or is of type Int; should be Bool."
;      (ck '(primapp or (bool true) (bool false))) -- 'Bool
;      (ck '(primapp or (bool true) (primapp and (bool true) (bool false))))
;        -- 'Bool
;      (ck '(primapp or (new Struct) (new Struct)))
;        -- "<error> check-L1-expr: first argument to or is of type Struct; should be Bool."
;      (ck '(primapp or
;                    (new Car (num 100) (num 1000))
;                    (new Vehicle (num 100))))
;        -- "<error> check-L1-expr: Incorrect number of fields in constructor: (new Vehicle (Int))"
;
;
;      )))

;;;;; New-style test code:

;(define preds '(type? type:function? type:method? type:struct-name?
;                      type:base? types-equal?))


;(define type-check-funs '(just-check-type extend-method-type
;                                          compare-argtype-lists))

;(define all-traceables (append preds subtype-rels
;                               type-check-funs))

;(define (go!)
;  (append (testall type-pred-tests preds)
;          (testall subtyping-tests subtype-rels)
;          (testall typecheck-tests type-check-funs)))

) ;; end module
