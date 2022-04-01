#!/cse/grads/jmj/bin/petite --script

(case-sensitive #t)
(source-directories '("." "src"))

(include "run-L0.ss")

(define use-repl #f)
(define show-transform #f)
(define BANNER
"     *** MultiCruz 2005 ***
By Jordan Johnson and Damian Eads
(for CMPS 203 -- Cormac Flanagan)~n~n")

;(trace preprocess/validate-L0-prog check-L1-prog check-L1-expr eval-L2-prog)
;; Reads a program (list of sexps) from current-input-port and returns them in
;; the order in which they were read.
(define (read-prog)
  (let loop ((prog '())
             (next-part (read)))
    (if (eof-object? next-part)
      (reverse prog)
      (loop (cons next-part prog) (read)))))

(printf BANNER)

(let ([args (command-line-arguments)])
  (when (not (null? args))
    (cond
      ((string=? (car args) "-r")
       (set! use-repl #t)
       (set! args (cdr args)))
      ((string=? (car args) "-t")
       (set! show-transform #t)
       (set! args (cdr args)))))
  (cond
    ((null? args) (run-repl show-transform))
    ((string=? (car args) "-h") ;; print usage and exit.
     (printf "usage: run.ss [-h|-r|-t] [file ...]
     0  args: run a REPL loop.
     1+ args: load and run each file, in sequence.~n")
     (printf "Options:
     -h         show this message
     -r         enter a repl when done evaluating any program files
     -t         show L0->L1->L2 transformations~n"))
    (else
      (let loop ((file (car args))
                 (rest (cdr args)))
        (printf "~n### ~s ###~n" file)
        (let ((prog (with-input-from-file file
                      (lambda () (read-prog)))))
          (pretty-print (run prog show-transform))
          (if (null? rest)
            (if use-repl (run-repl show-transform))
            (loop (car rest) (cdr rest))))))))

