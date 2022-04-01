;; vim:set ai lisp sm mat=2 ft=scheme:
;; File: test.ss
;;
;; Test-cases for muldisp.
;;
;; Authors: Damian Eads
;;          Jordan Johnson
;;
;; Date:    10/24/2005

(module (test test:list
         fn-test testall test-all/trace-failed tatf
         run-tests run-test run-untrapped-test
         trace-tests trap-errors)

(import scheme)
(include "pregexp.scm")
(include "helpers.ss")

;(print-level 5)
;(print-length 8)

;;;; Main interface for testing (refer to definitions of the following):
;;      test test:list fn-test test-all/trace-failed tatf

;; PARAMETER: traceables is a list of procedures that you would like to trace
;; (on failure) in test-all/trace-failed.  It can be bound with a fluid-let,
;; e.g.:
;;      (fluid-let ((traceables '(check-type assume assume* type-of)))
;;        (tatf <type-checker tests>))
;;
(define traceables '(run-test))

;; In all following code/text, "expr" refers to an expression in the defined
;; language being implemented; "scheme-expr" refers to an arbitrary Scheme
;; expression.

;; A test-triple is defined as a triple
;;      ((lambda () scheme-expr) scheme-expr scheme-expr)
;; where the first scheme-expr and the third scheme-expr should evaluate to
;; the same value[*], and the middle scheme-expr is a representation of the
;; first one to use when printing tests.
;;
;; [*] If the third scheme-expr is a string, it will be used as a regexp and
;; matched against the test's result (if that result is a string).  This is
;; particularly useful for error cases.

;;; Syntax/functions for building tests:

;; SYNTAX: (test e -- v) creates a test-triple mapping e to v.
(define-syntax test
  (syntax-rules (--)
    ((_ e -- v)
     (list (lambda () e) 'e v))
    ((_ . etc)
     (error 'test "Malformed test pair: ~a" '(_ . etc)))))

;; SYNTAX: (test:list expr0 -- val0
;;                    expr1 -- val1
;;                    ...)
;; Produces a list of test-triples from the given exprs and values.
(define-syntax test:list
  (syntax-rules (--)
    ((_ e0 -- v0)
     (list (test e0 -- v0)))
    ((_ e0 -- v0 . other-tests)
     (cons (test e0 -- v0)
           (test:list . other-tests)))))

;; 'a any ('b 'c ... -> 'a) . ('b 'c ...) -> test-triple
;; Generates a test-triple from the given args:  In the resulting test-triple,
;; the function fn must yield the value val when applied to fn-args.  expr is
;; used as the "show" expression in the cadr of the triple.
;; Useful for testing a language processor (e.g. interpreter or type-checker).
(define (fn-test val expr fn . fn-args)
  (list (lambda () (apply fn fn-args)) expr val))

;;; Functions for running tests:

;; A result is defined as a failed-result or #f.
;;      #f is a successful result.
;; A failed-result is a pair (test-triple . string-or-value) where the
;; test-triple is the attempted test and a string-or-value is defined as either:
;;      a string, which is an error message produced by an evaluation, or
;;      a value, which is an erroneous value produced by an evaluation.

;; listof[test] listof[sym] -> listof[result]
;; Runs test-all/trace-failed on the given test list, using the given list of
;; procedure names for tracing purposes.
(define (testall tlist procnames)
  (fluid-let ((traceables procnames))
    (tatf tlist)))

;; listof[test-triple] -> listof[failed-tests]
;; EFFECT: print a trace of all tests that failed.
(define (test-all/trace-failed ts)
  (let ((failed (run-tests ts)))
    (if (null? failed)
      (begin (printf "*** All tests passed. ***~%")
             '())
      (begin (printf "=== Failed tests: ===~%")
             (trace-tests (map car failed))))))

;; Alias:
(define tatf test-all/trace-failed)

;; listof[test] -> listof[failed-result]
;; Tests a list of tests and returns the failed-results of those that
;; fail.
(define (run-tests ts)
  (printf "Running tests...\n")
  (filter (lambda (x) x) (map run-test ts)))

;; test-triple -> result
;; Run one test.
(define (run-test t)
  ;(printf "\tRunning test ~a...\n" t)
  (let ((thunk (car t)) (the-expr (cadr t)) (desired-result (caddr t)))
  ;  (printf "\t\t1. ~a\n\t\t2. ~a\n\t\t3. ~a\n"
  ;          thunk the-expr desired-result)
    (let ((th-result (trap-errors thunk)))
      (cond
        ((equal? th-result desired-result) #f)                  ;; Success!
        ((and (string? th-result) (string? desired-result)
              (pregexp-match desired-result th-result))
         #f)                                    ;; Success via regexp match.
        (else
          (cons t th-result))))))               ;; Failure!

;; test-triple -> result
;; Run one test, without catching errors.
(define (run-untrapped-test t)
  (let ((thunk (car t)) (the-expr (cadr t)) (desired-result (caddr t)))
    (let ((th-result (thunk)))
      (if (equal? th-result desired-result)
        #f
        (cons t th-result)))))

;;;; Tests:

;; listof[tests][non-empty] -> listof[result]
;; EFFECT: Prints a trace of functions listed in the traceables parameter.
(define (trace-tests tests)
  (eval `(trace ,@traceables))
  (let ((results (run-tests tests)))
    (eval `(untrace ,@traceables))
    results))

;;;; Misc helpers:

;; (() -> 'a) -> (union 'a string)
;; Evaluates (thunk), trapping errors and returning error msgs as strings.
(define (trap-errors thunk)
  (call/cc
    (lambda (k)
      (parameterize ((print-level 3)
                     (print-length 6)
                     (error-handler
                       (lambda (who msg . args)
                         (k (format "<error> ~a~a"
                                    (if who (format "~s: " who) "")
                                    (apply format msg args))))))
        (thunk)))))

) ;; end module
