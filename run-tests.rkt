#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
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
(interp-tests "while" type-check-Lwhile compiler-passes interp-Lwhile "while_test" (tests-for "while"))
; (interp-tests "aman" type-check-Lwhile compiler-passes interp-Lwhile "aman_test" (tests-for "aman"))



;; Uncomment the following when all the passes are complete to test the final x86 code.
;;(compiler-tests "var" type-check-Lif compiler-passes "var_test" (tests-for "var"))

