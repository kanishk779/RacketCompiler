#lang racket
(require racket/set racket/stream)
(require racket/dict)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; The dictionary (i.e env) stores the mapping between the original variable names and the new corresponding variable name that we create using gensym function.
;; example (let [x 10] (+ x 10))  ----UNIQUIFY---> (let [x.1 10] (+ x.1 10)) where 'x' has been mapped to 'x.1' using the gensym function
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-name (gensym x))
       (define new-env (dict-set env x new-name))
       (Let new-name ((uniquify-exp new-env) e) ((uniquify-exp new-env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; Checks if an expression is atomic (i.e a variable or an integer)
(define (atom? exp)
  (match exp
    [(Var x) #t]
    [(Int n) #t]
    [_ #f]))

;; Converts the complex expressions to atomic expressions (Refer the grammar on page 27 for atomic expressions)
;; by introducing new variables using the Let feature of Racket.
(define (rco_atom exp)
  (match exp
    [(Prim '+ (list e1 e2))
     (cond
       [(and (atom? e1) (atom? e2))
        (define new-name (gensym "tmp"))
        (Let new-name (Prim '+ (list e1 e2)) (Var new-name))]
       [(and (not (atom? e1)) (not (atom? e2)))
        (define new-name-1 (gensym "tmp"))
        (define new-name-2 (gensym "tmp"))
        (Let new-name-1 (rco_exp e1) (Let new-name-2 (rco_exp e2) (Prim '+ (list (Var new-name-1) (Var new-name-2)))))]
       [(atom? e1)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e2) (Prim '+ (list e1 (Var new-name))))]
       [(atom? e2)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e1) (Prim '+ (list (Var new-name) e2)))]
       )]
    [(Prim '- (list e1))
     (define new-name (gensym "tmp"))
     (Let new-name (rco_exp e1) (Prim '- (list (Var new-name))))]))
    
;; Converts complex expression using the above function rco_atom only if there is a need to
;; introduce a new variable, for other cases rco_exp function handles the expression
(define (rco_exp exp)
  (match exp
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '+ (list e1 e2))
     (if (and (atom? e1) (atom? e2))
         (Prim '+ (list e1 e2))
         (rco_atom exp))]
    [(Prim '- (list e1))
     (if (atom? e1)
         (Prim '- (list e1))
         (rco_atom exp))]
    [(Let x e body)
     (Let x (rco_exp e) (rco_exp body))]))
         
(define (test_rco p)
  (assert "testing rco"
          (equal? (interp-Lvar p) (interp-Lvar (remove-complex-opera* p)))))

(define (random-test)
  (test_rco (parse-program `(program () (let ([y (let ([x 20]) (+ x (let ([x 22]) x)))]) y))))
  (test_rco (parse-program `(program () (let ([x (+ 10 (+ 5 6))]) (+ (+ x 1) 10)))))
  (test_rco (parse-program `(program () (let ([x 20]) (+ x (let ([x 22]) (+ x 10)))))))
  )
;; remove-complex-opera* : R1 -> R1
    
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))

;; The input to this pass will be the L_var with all the complex operation removed
;; which means operands of each operation will be atoms, (i.e Var or Int)
(define (explicate-tail exp)
  (match exp
    [(Var x) (values (Return (Var x)) (list))]
    [(Int n) (values (Return (Int n)) (list))]
    [(Prim op es) (values (Return (Prim op es)) (list))]
    [(Let x rhs body)
     (define-values (tail-exp var-list) (explicate-tail body))
     (explicate-assign rhs x tail-exp var-list)]
    [_ (error "explicate-tail unhandled case" exp)]))

;; This function is for the creating assignment statement in C_var language (Refer the grammar)
(define (explicate-assign exp x cont var-list)
  (match exp
    [(Var var)
     (values (Seq (Assign (Var x) (Var var)) cont) (cons x var-list))]
    [(Int n)
     (values (Seq (Assign (Var x) (Int n)) cont) (cons x var-list))]
    [(Prim op es)
     (values (Seq (Assign (Var x) (Prim op es)) cont) (cons x var-list))]
    [(Let y rhs body)
     (define-values (tail-exp new-var-list) (explicate-assign body x cont var-list))
     (explicate-assign rhs y tail-exp new-var-list)]
    [_ (error "explicate-assign unhandled case" exp)]))


;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (tail-exp var-list) (explicate-tail e))
     (define exp-dict (dict-set '() 'start tail-exp))
     (define info-dict (dict-set '() 'locals var-list))
     (CProgram info-dict exp-dict)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

