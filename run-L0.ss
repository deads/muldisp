;; vim:set ai lisp sm mat=2 ft=scheme:
;; File: run-L0.ss
;;
;; Framework for running an entire program, from preproc to evaluation.
;;
;; Author: Jordan Johnson
;;
;; Date:    Tue Nov 29 17:05:11 PST 2005

(case-sensitive #t)

(source-directories '("." "src"))
(module (run run-repl)
(include "src/match.ss")
(include "src/env.ss")
(include "src/context.ss")

(include "src/preprocessor.ss")
(include "src/typecheck.ss")
(include "src/interpreter.ss")

(import preprocessor)
(import typecheck)
(import interpreter)

;; L0-prog bool -> L2-val
(define (run prog show-transform)
  (let* ((L1-prog (preprocess/validate-L0-prog prog))
         (L2-prog (begin (when show-transform
                           (printf " === L1 program: ===~n")
                           (pretty-print L1-prog))
                         (check-L1-prog L1-prog))))
    (when show-transform
      (printf " === L2 program: ===~n")
      (pretty-print L2-prog))
    (eval-L2-prog L2-prog (empty-env) (empty-env) (empty-env))))

;; bool -> ()
(define (run-repl show-transform)
  (let ((env (empty-env))
        (context (empty-context))
        (struct-env (empty-env))
        (method-env (empty-env)))

    ;; This function is necessary for when the user defs a new method
    ;; (first time, no existing defs):
    (define (def-emptyMM-if-needed defn) ; L1 -> void
      (match defn                        ; but may extend method-env
        [(def ,mname : ,T ,e)
         (cond
           ((apply-env method-env mname)
             => (lambda (val)
                  (when show-transform
                    (if (eq? val 'EmptyMM)
                      (printf "(Overriding empty method ~a.)~n" mname)
                      (printf "(Overriding method ~a.)~n" mname)))))
           (else
             (when show-transform
               (printf "(Implicitly defining ~a as empty method.)~n" mname))
             (set! method-env (extend-env method-env mname 'EmptyMM))
             (set! context (assume mname '(method) context))))]
        [,other-defn-type       ;; do nothing for struct/var defns...
         (void)]))

    ;; expr/defn -> value or 'OK.
    ;; EFFECT: may mutatively extend one of the four envs/ctxs above
    (define (run-one expr/defn)
      (if (and (pair? expr/defn)
               (memq (car expr/defn) '(def-struct defm def)))
        ;; Eval as defn:
        (let ((L1-defn (preprocess/validate-L0-defn expr/defn)))
          (printf " -> L1 defn = <~a>~n" L1-defn)
          (let-values ([(L2-defn L2-defn-type new-ctx new-se-DISCARD)
                        (begin (def-emptyMM-if-needed L1-defn)
                               (check-L1-defn L1-defn context struct-env))])
            (when show-transform
              (printf "\t-> L2 defn:~n")
              (pretty-print L2-defn)
              (printf "\t   Type : ~a~n" L2-defn-type))
            (let-values ([(new-env new-se new-me)
                          (eval-L2-defn L2-defn env struct-env method-env)])
              (set! env new-env)
              (set! context new-ctx)
              (set! struct-env new-se)
              (set! method-env new-me)
              L2-defn-type)))
        ;; Eval as expr:
        (let ((L1-expr (preprocess/validate-L0-expr expr/defn)))
          (when show-transform
            (printf " -> L1 expr:~n")
            (pretty-print L1-expr))
          (let-values ([(L2-expr T)
                        (check-L1-expr L1-expr context struct-env)])
            (when show-transform
              (printf "   -> L2 expr:~n")
              (pretty-print L2-expr )
              (printf "      Type : ~a~n" T))
            (eval-L2-expr L2-expr env struct-env method-env)))))

    (parameterize ((waiter-prompt-string ">>"))
      (new-cafe (lambda (x)
                  (if (equal? x '(debug))
                    (debug)
                    (run-one x)))))))

) ;; end module
