#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "interp-Cvec.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "interp-Lvec-prime.rkt")
; (require "type-check-Lvec-prime.rkt")
(debug-level 1)
(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

;; NOTE -> we can replace "var" with "if" and vice-versa for testing different versions of the languages

;; Replace the #f with the type-checker
;(interp-tests "vec" type-check-Lvec compiler-passes interp-Lvec "vec_test" (tests-for "vec"))
; (interp-tests "aman" type-check-Lvec compiler-passes interp-Lvec "aman_test" (tests-for "aman"))

; (interp-tests "var" #f compiler-passes interp-Lvar "var_test" (tests-for "var"))



;; Uncomment the following when all the passes are complete to test the final x86 code.
(compiler-tests "vec" type-check-Lvec compiler-passes "vec_test" (tests-for "vec"))

