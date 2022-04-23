#lang racket
(require racket/set racket/stream)
(require racket/dict)
(require racket/fixnum)

(require graph)
(require data/queue)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Cvec.rkt")
(require "interp-Cif.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Cvec.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Lfun.rkt")
(require "interp-Cvec.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lvec-prime.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
; (AST-output-syntax 'abstract-synta)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Int n) e]
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

(define (shrink-exp exp)
  (match exp
    [(Int int) exp]
    [(Bool b) exp]
    [(Void) exp]
    [(Var var) exp]
    [(If e1 e2 e3)
     (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [(Let x e body)
     (Let x (shrink-exp e) (shrink-exp body))]
    [(SetBang var rhs) (SetBang var (shrink-exp rhs))]
    [(WhileLoop cnd body)
     (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [(Begin es body)
     (define new-exp-list (for/list ([e es]) (shrink-exp e)))
     (Begin new-exp-list (shrink-exp body))]
    [(Prim 'and (list e1 e2))
     (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (shrink-exp e)))]
    [(HasType es type)
     (HasType (shrink-exp es) type)]
    [(Apply fun args)
     (define arg-vals (for/list ([e args]) (shrink-exp e)))
     (Apply (shrink-exp fun) arg-vals)]
    [(Def fun param* rt info body)
     (Def fun param* rt info (shrink-exp body))]
    [_ (error "Error: Unidentified Case in shrink-exp")]
    ))

;; Shrink : L_if -> L_if
(define (shrink p)
  (match p
    [(ProgramDefsExp info ds body)
     (let ([top-level (for/list ([d ds]) (shrink-exp d))])
       (ProgramDefs info (append top-level (list (Def 'main '() 'Integer '() (shrink-exp body))))))]
    [(Program info e)   (Program info (shrink-exp e))]  ;; I think we should remove this  :: I think so too
    [_ (error "Error : Unidentified Case in shrink")]))

;; The dictionary (i.e env) stores the mapping between the original variable names and the new corresponding variable name that we create using gensym function.
;; example (let [x 10] (+ x 10))  ----UNIQUIFY---> (let [x.1 10] (+ x.1 10)) where 'x' has been mapped to 'x.1' using the gensym function
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(If e1 e2 e3)
       (define e1^ ((uniquify-exp env) e1))
       (define e2^ ((uniquify-exp env) e2))
       (define e3^ ((uniquify-exp env) e3))
       (If e1^ e2^ e3^)]
      [(SetBang var rhs)
       (SetBang (dict-ref env var) ((uniquify-exp env) rhs))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Begin es body)
       (define new-exp-list (for/list ([e es]) ((uniquify-exp env) e)))
       (Begin new-exp-list ((uniquify-exp env) body))]
      [(Let x e body)
       (define rhs ((uniquify-exp env) e))
       (define new-name (gensym x))
       (define new-env (dict-set env x new-name))
       (Let new-name rhs ((uniquify-exp new-env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(HasType ex t)
       (HasType ((uniquify-exp env) ex) t)]
      [(Apply fun args)
       (Apply ((uniquify-exp env) fun) (map (uniquify-exp env) args))]
      [(Def name param* rt info body)
       (define new-param (match param*
                           [(list `[,xs : ,ps] ...)
                            (for/list ([x xs] [p ps]) `[,(dict-ref env x) : ,p])]))  ;; changing the names of parameters using the environment
       (Def (dict-ref env name) new-param rt info ((uniquify-exp env) body))]
      [_ (error "Error: Unidentified Case in uniquify-exp")])))

;; generate environment for the function, basically add the parameters info into environment
(define (give-env d)
  (match d
    [(Def name (list `[,xs : ,ps] ...) rt info body)
     (for/list ([x xs]) (cons x (gensym x)))]
    [_ (error "Error: Unidentified case in give-env")]))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info ds)
     (define base-env (map (lambda (d) (cons (Def-name d) (Def-name d))) ds)) ;; base-env creates a dictionary which maps each function name to itself.
     (let ([new-ds (for/list ([d ds]) ((uniquify-exp (append base-env (give-env d))) d))]) ;; Append the base env with new environment for this particular function
       (ProgramDefs info new-ds))]
    [(Program info e) (Program info ((uniquify-exp '()) e))]
    [_ (error "Error: Unidentified Case in uniquify")]))

;; reveal function calls in each function definition
(define (reveal-function-exp d )
  (match d
    [(Int int) d]
    [(Bool b) d]
    [(Void) d]
    [(Var var) d]
    [(If e1 e2 e3)
     (If (reveal-function-exp e1 ) (reveal-function-exp e2 ) (reveal-function-exp e3 ))]
    [(Let x e body)
     (Let x (reveal-function-exp e ) (reveal-function-exp body ))]
    [(SetBang var rhs)
     (SetBang var (reveal-function-exp rhs ))]
    [(WhileLoop cnd body)
     (WhileLoop (reveal-function-exp cnd ) (reveal-function-exp body ))]
    [(Begin es body)
     (define new-exp-list (for/list ([e es]) (reveal-function-exp e )))
     (Begin new-exp-list (reveal-function-exp body ))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (reveal-function-exp e )))]
    [(HasType es type)
     (HasType (reveal-function-exp es ) type)]
    [(Apply fun args)
     (define arg-vals (for/list ([e args]) (reveal-function-exp e )))
     (match fun
       [(Var var) (Apply (FunRef var) arg-vals)]
       [_ (Apply (reveal-function-exp fun) arg-vals)])]
    [(Def fun param* rt info body)
     (Def fun param* rt info (reveal-function-exp body ))]
    [_ (error "Error: Unidentified Case in reveal-function-exp")]
    ))

;; Reveal functions
(define (reveal-function p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (reveal-function-exp d )))
     (ProgramDefs info new-ds)]
    [_ (error "Error: Unidentified Case in reveal-function")]))

;; Limit function expression
(define (limit-function-exp vec in-vector body)
  (match body
    [(Int int) (Int int)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(FunRef fun)
     (if (member fun in-vector)
         (Prim 'vector-ref (list (Var vec) (Int (index-of in-vector fun))))
         (FunRef fun))]
    [(Var var)
     (if (member var in-vector)
         (Prim 'vector-ref (list (Var vec) (Int (index-of in-vector var))))
         (Var var))]
    [(If e1 e2 e3)
     (If (limit-function-exp vec in-vector e1 ) (limit-function-exp vec in-vector e2 ) (limit-function-exp vec in-vector e3 ))]
    [(Let x e body)
     (Let x (limit-function-exp vec in-vector e) (limit-function-exp vec in-vector body))]
    [(SetBang var rhs)
     (if (member var in-vector)
         (Prim 'vector-set! (list (Var vec) (Int (index-of in-vector var)) (limit-function-exp vec in-vector rhs)))
         (SetBang var (limit-function-exp vec in-vector rhs)))]
    [(WhileLoop cnd body)
     (WhileLoop (limit-function-exp vec in-vector cnd) (limit-function-exp vec in-vector body))]
    [(Begin es body)
     (define new-exp-list (for/list ([e es]) (limit-function-exp vec in-vector e)))
     (Begin new-exp-list (limit-function-exp vec in-vector body))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (limit-function-exp vec in-vector e)))]
    [(HasType es type)
     (HasType (limit-function-exp vec in-vector es) type)]
    [(Apply fun args)
     (define new-args (if (> (length args) 6)
                          (append (take args 5) (list (Prim 'vector (drop args 5))))
                          args))
     (define args^ (for/list ([arg new-args]) (limit-function-exp vec in-vector arg)))
     (Apply (limit-function-exp vec in-vector fun)  args^)]))

;; Limit functions definition for top-level functions
(define (limit-function-def d)
  (match d
    [(Def fun param rt info body)
      ; (printf "\nThe param variable has ~a\n" param)
     (define vec (gensym 'arg-vec))   ;; give a new name to the generated vector
     (define types (map caddr param)) ;; extract the types out from param
     (define in-vector (if (> (length param) 6)
                           (map car (drop param 5)) ;; Name of variables which will be in the vector
                           (list)))
     (define new-param (if (> (length param) 6)
                           (append (take param 5) `((,vec : ,(cons 'Vector (drop types 5)))))
                           param))
     (Def fun new-param rt info (limit-function-exp vec in-vector body))]
    [_ (error "Error: Unidentified case in limit-function-def")]))

;; Limit functions
(define (limit-function p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (limit-function-def d)))
     (ProgramDefs info new-ds)]
    [_ (error "Error: Unidentified case in limit-function")]))

;; collects all the variables which are mutating
(define (collect-set! exp)
  (match exp
    [(Var x) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Void) (set)]
    [(FunRef f) (set)]
    [(Let x e body)
     (set-union (collect-set! e) (collect-set! body))]
    [(If e1 e2 e3)
     (set-union (collect-set! e1) (collect-set! e2) (collect-set! e3))]
    [(SetBang var rhs)
     (set-union (set var) (collect-set! rhs))]
    [(WhileLoop cnd body)
     (set-union (collect-set! cnd) (collect-set! body))]
    [(Begin es body)
     (set-union (foldl set-union (set) (for/list ([e es]) (collect-set! e))) (collect-set! body))]
    [(Prim op es)
     (foldl set-union (set) (for/list ([e es]) (collect-set! e)))]
    [(HasType ex t) (collect-set! ex)]
    [(Def name param rt info body)
     (collect-set! body)]
    [(Apply fun args)
     (define new-arg (foldl set-union (set) (for/list ([arg args]) (collect-set! arg))))
     (set-union (collect-set! fun) new-arg)]
    [_ (error "Error: Unidentified Case in collect-set!" exp)]))

;; Replace the occurences of mutable variables with GetBang
(define ((uncover-get! vars) exp)
  (match exp
    [(Var x)
     (if (set-member? vars x)
         (GetBang x)
         (Var x))]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x e body)
     (Let x ((uncover-get! vars) e) ((uncover-get! vars) body))]
    [(If e1 e2 e3)
     (If ((uncover-get! vars) e1) ((uncover-get! vars) e2) ((uncover-get! vars) e3))]
    [(SetBang var rhs)
     (SetBang var ((uncover-get! vars) rhs))]
    [(WhileLoop cnd body)
     (WhileLoop ((uncover-get! vars) cnd) ((uncover-get! vars) body))]
    [(Begin es body)
     (define new-es (for/list ([e es]) ((uncover-get! vars) e)))
     (Begin new-es ((uncover-get! vars) body))]
    [(Prim op es)
     (Prim op (for/list ([e es]) ((uncover-get! vars) e)))]
    [(HasType ex t) (HasType ((uncover-get! vars) ex) t)]
    [(Def name param rt info body)
     (Def name param rt info ((uncover-get! vars) body))]
    [(FunRef f) (FunRef f)]
    [(Apply fun arg)
     (Apply ((uncover-get! vars) fun) (map (uncover-get! vars) arg))]
    [_ (error "Error: Unidentified Case in uncover-get!")]))

;; uncover-get
(define (uncover-get p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (let ([vars (collect-set! d)]) ((uncover-get! vars) d))))
     (ProgramDefs info new-ds)]
    [(Program info e)
     (define vars (collect-set! e))
     (Program info ((uncover-get! vars) e))]
    [_ (error "Error: Unidentified Case in uncover-get")]))

(define (expose-allocation-exp exp)
  ; (printf "\nExpose allocation processing ~a\n" exp)
  (match exp
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x e body)
     (Let x (expose-allocation-exp e) (expose-allocation-exp body))]
    [(FunRef f)       (FunRef f)]
    [(Apply fun arg) (Apply (expose-allocation-exp fun) (map expose-allocation-exp arg))]
    [(If e1 e2 e3)
     (If (expose-allocation-exp e1) (expose-allocation-exp e2) (expose-allocation-exp e3))]
    [(SetBang var rhs)
     (SetBang var (expose-allocation-exp rhs))]
    [(GetBang var) (GetBang var)]
    [(WhileLoop cnd body)
     (WhileLoop (expose-allocation-exp cnd) (expose-allocation-exp body))]
    [(Begin es body)
     (define new-es (for/list ([e es]) (expose-allocation-exp e)))
     (Begin new-es (expose-allocation-exp body))]
    [(Prim 'vector-ref (list e int))
     (Prim 'vector-ref (list (expose-allocation-exp e) int))]
    [(Prim 'vector-set! (list e1 int e2))
     (Prim 'vector-set! (list (expose-allocation-exp e1) int (expose-allocation-exp e2)))]
    [(Prim 'vector-length (list e))
     (Prim 'vector-length (list (expose-allocation-exp e)))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (expose-allocation-exp e)))]
    [(HasType (Prim 'vector e) type)
      ; (printf "\nEntered HasType\n")
       (define i 0)
       (define bytes (* 8 (length e)))
       (foldl
        (lambda (elem acc)
          (let* ([x (string->symbol (string-append "x" (number->string i)))]
	        [q (Let x (expose-allocation-exp elem) acc)])
            (set! i (+ 1 i))
            q))
        (let ([q (Let (gensym '_)
                      (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes))) (GlobalValue 'fromspace_end)))
                          (Void)
                          (Collect bytes))
                      (Let 'v (Allocate (length e) type)
                           (foldl
                            (lambda (elem acc)
                              (let* ([x (string->symbol (string-append "x" (number->string i)))]
                                     [q (Let (gensym '_) (Prim 'vector-set! (list (HasType (Var 'v) type) (Int i) (Var x))) acc)])
                                (set! i (+ 1 i))
                                q
                               )
                              )
                            (begin (set! i 0) (HasType (Var 'v) type))
                          (map expose-allocation-exp e)))
                      )
                 ]
              )
          (begin (set! i 0) q)
          )
        e)]
    [(HasType e t)
     (HasType (expose-allocation-exp e) t)]
    [(Def name param rt info body)
     (Def name param rt info (expose-allocation-exp body))]
    [_ (error "Error: Unidentified Case in expose allocation!")]))

(define (expose-allocation p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (expose-allocation-exp d)))
     (ProgramDefs info new-ds)]
    [(Program info e)
     (Program info (expose-allocation-exp e))]
    [_ (error "Error: Unidentified Case in expose allocation")]))

;; Checks if an expression is atomic (i.e a variable or an integer)
(define (atom? exp)
  (match exp
    [(Var x) #t]
    [(Int n) #t]
    [(Bool b) #t]
    [(Void) #t]
    [_ #f]))

;; creates a list for arguments of Apply struct
(define (make-list-apply len curr)
  (if (eq? curr len)
      (list)
      (cons (Var (string->symbol (string-append "x" (number->string curr)))) (make-list-apply len (+ curr 1)))))

;; Converts the complex expressions to atomic expressions (Refer the grammar on page 27 for atomic expressions)
;; by introducing new variables using the Let feature of Racket.
(define (rco_atom exp)
  ; (printf "\nRco atom processing ~a\n" exp)
  (match exp
    [(FunRef fun)
     (define new-name (gensym 'fun))
     (Let new-name (FunRef fun) (Var new-name))] ;; Not sure if it is correct
    [(Apply fun args)
      (define new-args (map rco_exp args))
     (define new-name (gensym 'fun))
     (define i 0)
     (define output (foldl
      (lambda (elem acc)
        (let* ([x (string->symbol (string-append "x" (number->string i)))]
               [q (Let x (list-ref new-args i) acc)])
          (set! i (+ 1 i))
          q
          )
        )
      (begin (set! i 0)
             (match fun
              ;  [(FunRef var) (Apply fun (make-list-apply (length args) 0))]
               [_ (Let new-name (rco_exp fun) (Apply (Var new-name) (make-list-apply (length args) 0)))]
               ))
      new-args))
      ; (printf "Rco atom gives us ~a\n" output)
      output]
     
    [(Prim op (list e1 e2))
     (cond
       [(and (not (atom? e1)) (not (atom? e2)))
        (define new-name-1 (gensym "tmp"))
        (define new-name-2 (gensym "tmp"))
        (Let new-name-1 (rco_exp e1)
             (Let new-name-2 (rco_exp e2)
                  (Prim op (list (Var new-name-1) (Var new-name-2)))))]
       [(atom? e1)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e2)
             (Prim op (list e1 (Var new-name))))]
       [(atom? e2)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e1)
             (Prim op (list (Var new-name) e2)))]
       )]
    [(Prim op (list e1))
     (define new-name (gensym "tmp"))
     (Let new-name (rco_exp e1)
          (Prim op (list (Var new-name))))]
    [else (error "Error: Unidentified Case in rco_atom")]))
    
;; Converts complex expression using the above function rco_atom, only if there is a need to
;; introduce a new variable, for other cases rco_exp function handles the expression
;; READ rco_exp --- output ---> As an expression which does not contain any complex operation,
;; but it might not necessarily be an atom.
(define (rco_exp exp)
  ; (printf "\nRco exp processing ~a\n" exp)
  (match exp
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(GetBang var) (GetBang var)]
    
    [(SetBang var rhs) (SetBang var (rco_exp rhs))]
    [(Begin es body)
     (define new-exp (for/list ([e es]) (rco_exp e)))
     (Begin new-exp (rco_exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (rco_exp cnd) (rco_exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim 'vector-set! (list e1 int e2)) 
      (cond
       [(and (not (atom? e1)) (not (atom? e2)))
        (define new-name-1 (gensym "tmp"))
        (define new-name-2 (gensym "tmp"))
        (Let new-name-1 (rco_exp e1)
             (Let new-name-2 (rco_exp e2)
                  (Prim 'vector-set! (list (Var new-name-1) int (Var new-name-2)))))]
       [(atom? e1)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e2)
             (Prim 'vector-set! (list e1 int (Var new-name))))]
       [(atom? e2)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e1) (Prim 'vector-set! (list (Var new-name) int e2)))]
       )]
    [(Prim 'vector-ref (list e1 int)) 
      (define new-name (gensym "tmp"))
      (Let new-name (rco_exp e1) (Prim 'vector-ref (list (Var new-name) int)))]
    [(Prim 'vector-length (list e)) 
      (define new-name (gensym "tmp"))
      (Let new-name (rco_exp e) (Prim 'vector-length (list (Var new-name))))] 
    ;; This will cover,  not, - (unary) 
    [(Prim op (list e1))
     (if (atom? e1)
         (Prim op (list e1))
         (rco_atom exp))]
    ;; This will cover, eq?, <, >, <= , >=, +, - (binary)
    [(Prim op (list e1 e2))
     (if (and (atom? e1) (atom? e2))
         (Prim op (list e1 e2))
         (rco_atom exp))]    
    [(If cnd thn els)  ;; We need to check, why the book mentions not to replace the condition with a variable
     (If (rco_exp cnd) (rco_exp thn) (rco_exp els))]
    [(Let x e body)
     (Let x (rco_exp e) (rco_exp body))]
    [(Collect n) (Collect n)]
    [(GlobalValue name) (GlobalValue name)]
    [(Def fun param rt info body)
     (Def fun param rt info (rco_exp body))]
    [(FunRef fun) (FunRef fun)]
    [(Apply fun args) (rco_atom exp)]
    [(Allocate n t) (Allocate n t)]
    [(HasType e t)
     (HasType (rco_exp e) t)]
    [_  (error "Error: Unidentified case in rco_exp")]))
         
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
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (rco_exp d)))
     (ProgramDefs info new-ds)]
    [(Program info e) (Program info (rco_exp e))]
    [_ (error "Error: Unidentified case in remove-complex-opera*")]))

;; The global alist for blocks
(define basic-blocks (list))

;; Create new-blocks
(define (create-block tail)
  (match tail
    [(Goto label) tail]
    [_
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]
    ))

;; Create block with given name
(define (create-block-name tail name)
  (set! basic-blocks (cons (cons name tail) basic-blocks))
  (Goto name))

;; explicate-effect-list handles a list of expressions in effect position
(define (explicate-effect-list exp cont)
  (match exp
    [(list) (values cont (list))]
    [_
     (define-values (new-cont var-list) (explicate-effect-list (cdr exp) cont))
     (define-values (stmt var-lst) (explicate-effect (car exp) new-cont))
     (values stmt (append var-lst var-list))]))

;; explicate-effect for handling side-effects returns stmts and var-list
(define (explicate-effect exp cont)
  (match exp
    [(Int n) (values cont (list))]
    [(Var x) (values cont (list))]
    [(Bool b) (values cont (list))]
    [(Void) (values cont (list))]
    [(GetBang var) (values cont (list))]
    [(SetBang var rhs)
     (explicate-assign rhs var cont (list))]
    [(Prim 'read es)                              ;; Read can be statement now
     (values (Seq (Prim 'read es) cont) (list))]
    [exp-list #:when (list? exp-list)
     (explicate-effect-list exp cont)]
    [(If cnd thn els) ;; Recursively call on then and else block
     (define-values (thn^ var-thn) (explicate-effect thn cont))
     (define-values (els^ els-thn) (explicate-effect els cont))
     (define thn-block (create-block thn^))
     (define els-block (create-block els^))
     (define-values (stmt var-lst) (explicate-pred cnd thn-block els-block))
     (values stmt (append var-lst var-thn els-thn))]
    [(Let x rhs body)
     (define-values (body^ var-lst) (explicate-effect body cont))
     (explicate-assign rhs x body^ var-lst)]
    [(Begin es body)
     (define-values (body^ var-list) (explicate-effect body cont))
     (define-values (stmt var-lst) (explicate-effect-list es body^))
     (values stmt (append var-list var-lst))]
    [(WhileLoop cnd body)
     (define loop-name (gensym 'loop))
     (define-values (body^ var-list) (explicate-effect body (Goto loop-name)))
     (define body-block (create-block body^))
     (define cont-block (create-block cont))
     (define-values (stmt var-lst) (explicate-pred cnd body-block cont-block))
     (define loop-block (create-block-name stmt loop-name))
     (values
      (Goto loop-name)
      (append var-lst var-list))]
    [(Prim 'vector-set! es)
     (values
      (Seq
       (Assign (Var (gensym '_)) (Prim 'vector-set! es)) cont)
      (list))]
    [(Prim op es)
     (values cont (list))]
    [(FunRef l)
     (values
      (Seq
       (Assign (Var (gensym '_)) (FunRef l)) cont)
      (list))]
    [(Apply fn arg)
     (values
      (Seq
       (Assign (Var (gensym '_)) (Call fn arg)) cont)
      (list))]
    [_ (error "Error: Unidentified Case in explicate-effect" exp)]))
     
(define vector-list '())     
;; explicate-pred for handling the if statements
(define (explicate-pred cnd thn-block els-block)
  (match cnd
    [(Var var)
     (values
      (IfStmt (Prim 'eq? (list (Var var) (Bool #t)))
             thn-block
             els-block)
      (list))]
    [(GetBang var)
     (values
      (IfStmt (Prim 'eq? (list (Var var) (Bool #t)))
              thn-block
              els-block)
      (list))]
    [(Bool b) (values (if b thn-block els-block) (list))]
    [(Prim 'not (list x))
     (values
      (IfStmt (Prim 'eq? (list x (Bool #f)))
             thn-block
             els-block)
      (list))]
    [(Begin es body)
     (define-values (stmt var-list) (explicate-pred body thn-block els-block))
     (define-values (stmt^ var-lst) (explicate-effect es stmt))
     (values stmt^ (append var-list var-lst))]
    [(Prim op es)   ;; Takes care of eq?, <, >, >=, <=
     (values
      (IfStmt (Prim op es)
             thn-block
             els-block)
      (list))]
    [(Apply fn args)
      (define tem (gensym 'temp))
      (values
        (Seq (Assign (Var tem) (Call fn args)) 
          (IfStmt (Prim 'eq? (list (Var tem) (Bool #t)))
              thn-block
              els-block))
        (list))]
    [(Let x rhs body)
     (define-values (stmt var-list) (explicate-pred body thn-block els-block))
     (explicate-assign rhs x stmt var-list)]
    [(If cnd^ thn^ els^)
     (define-values (thn-stmt thn-list) (explicate-pred thn^ thn-block els-block))
     (define-values (els-stmt els-list) (explicate-pred els^ thn-block els-block))
     (define thn^-block (create-block thn-stmt))
     (define els^-block (create-block els-stmt))
     (define-values (stmt var-list) (explicate-pred cnd^ thn^-block els^-block))
     (values
      stmt
      (append thn-list els-list var-list))]
    [_ (error "explicate-pred unhandled case for cnd" cnd)])) 

;; The input to this pass will be the L_var with all the complex operation removed
;; which means operands of each operation will be atoms, (i.e Var or Int)
;; This is used to generate the tail in the grammar on page 25

(define (explicate-tail exp)
  (match exp ;; We assume that WhileLoop, SetBang will not be in tail position --> because all our programs should produce Integers.
    [(Var x)
     (values
      (Return (Var x)) (list))]
    [(Void)  ;; This will most likely will never be used.
     (values
      (Return (Void)) (list))]
    [(Int n)
     (values
      (Return (Int n)) (list))]
    [(Prim op es)
     (values
      (Return (Prim op es)) (list))]
    [(GetBang var)  ;; Need to verify whether we can get rid of GetBang after RCO (which I am doing currently)
     (values
      (Return (Var var)) (list))]
    [(Begin es body)
    ;  (printf "Begin es ~a  body ~a\n" es body)
     (define-values (tail-exp var-list) (explicate-tail body))
     (define-values (new-tail var-lst) (explicate-effect es tail-exp)) ;; explicate-effect takes a list of expression and cont stmts, returns a tail-expr
     (values new-tail (append var-list var-lst))]
    [(If cnd thn els)
     (define-values (thn^ var-thn) (explicate-tail thn))
     (define-values (els^ var-els) (explicate-tail els))
     (define thn-block (create-block thn^))
     (define els-block (create-block els^))
     (match cnd
       [(Bool b)
        (values
         (if b thn-block els-block)
         (if b var-thn var-els))]
       [_
        (define-values (stmt var-lst) (explicate-pred cnd thn-block els-block))
        (values
         stmt
         (append var-thn var-els var-lst))]
       )]
    [(Let x rhs body)
     (define-values (tail-exp var-list) (explicate-tail body))
     (explicate-assign rhs x tail-exp var-list)]
    [(Bool b)
     (values (Return (Bool b)) (list))]
    [(FunRef l)
     (values (Return (FunRef l)) (list))]
    [(Apply fn arg)
     (values (TailCall fn arg) (list))]
    [(HasType e t) (explicate-tail e)]
 
    [_ (error "explicate-tail unhandled case" exp)]))

;; This function is for the creating assignment statement in C_var language (Refer the grammar on Page 25)
(define (explicate-assign exp x cont var-list)
  (match exp
    [(Var var)
      (cond 
        [(member var vector-list) (set! vector-list (append vector-list (list x)))])
     (values
      (Seq
       (Assign (Var x) (Var var)) cont)
      (cons x var-list))]
    [(GetBang var)
     (values
      (Seq
       (Assign (Var x) (Var var)) cont)
      (cons x var-list))]
    [(SetBang var rhs)
     (define-values (rhs^ var-lst) (explicate-assign rhs var cont var-list))
     (values
      (Seq
       (Assign (Var x) (Void)) rhs^)
      (cons x var-lst))]
    [(Bool b)
     (values
      (Seq
       (Assign (Var x) (Bool b)) cont)
      (cons x var-list))]
    [(Int n)
     (values
      (Seq
       (Assign (Var x) (Int n)) cont)
      (cons x var-list))]
    [(Prim op es)
     (values
      (Seq
       (Assign (Var x) (Prim op es)) cont)
      (cons x var-list))]
    [(Begin es body)
     (define-values (body^ var-lst) (explicate-assign body x cont var-list))
     (define-values (new-cont var-effect) (explicate-effect es body^))
     (values new-cont (append var-lst var-effect))]
    [(WhileLoop cnd body)
     (define loop-name (gensym 'loop))
     (define-values (body^ var-effect) (explicate-effect body (Goto loop-name)))
     (define body-block (create-block body^))
     (define cont-block (create-block cont))
     (define-values (stmt var-lst) (explicate-pred cnd body-block cont-block))
     (define loop-block (create-block-name stmt loop-name))
     (values
      (Seq
       (Assign (Var x) (Void)) (Goto loop-name))
      (append var-lst var-list var-effect))]
    [(If cnd thn els)
     (define new-block (create-block cont))
     (define-values (thn^ var-thn) (explicate-assign thn x new-block var-list))
     (define-values (els^ var-els) (explicate-assign els x new-block var-list))
     (define thn-block (create-block thn^))
     (define els-block (create-block els^))
     (match cnd   ;; handle the variable lists, if the then or else block is not being used, some variable will not be needed
       [(Bool b)
        (values
         (if b thn-block els-block)
         (if b (append var-thn var-list) (append var-list var-els)))]
       [_
        (define-values (stmt var-lst) (explicate-pred cnd thn-block els-block))
        (values
         stmt
         (append var-thn var-els var-list var-list))])]   
    [(Let y rhs body)
        
     (define-values (new-exp new-var-list) (explicate-assign body x cont var-list))
     (explicate-assign rhs y new-exp new-var-list)]
    [(Collect n)
     (values (Seq (Collect n) cont)
      (cons x var-list))]
    [(Allocate n t)
     (set! vector-list (append vector-list (list x)))
     (values (Seq (Assign (Var x) (Allocate n t)) cont) 
     (cons x var-list))]
    [(GlobalValue name)
     (values (Seq (Assign (Var x) (GlobalValue name)) cont) (
        cons x var-list))]
    [(Void)
     (values (Seq (Assign (Var x) (Void)) cont) 
     (cons x var-list))]
    [(FunRef l)
     (values (Seq (Assign (Var x) (FunRef l)) cont)
      (cons x var-list))]
    [(Apply fn arg)
     (values (Seq (Assign (Var x) (Call fn arg)) cont)
      (cons x var-list))]
    [(HasType v t)  (set! vector-list (append vector-list (list v)))
                    (set! vector-list (append vector-list (list x)))
                    (explicate-assign v x cont var-list)]
    [_ (error "explicate-assign unhandled case" exp)]))

;; What is this used for??
(define (pick_v ele acc)
  (cond
    [(empty? ele) acc]
    [(symbol? (car ele)) (define f (first (string->list (symbol->string (car ele)))))
                          (match f
                            [#\v (pick_v (cdr ele) (append (list (car ele)) acc))]
                            [_ (pick_v (cdr ele) acc)])]
    [else (pick_v (cdr ele) acc)]))

;; What is this used for ??
(define (make-vector-list veclist varlist)
    (if (empty? veclist)
        (list)
        (if (member (car veclist) varlist)
            (cons (car veclist) (make-vector-list (cdr veclist) varlist))
            (make-vector-list (cdr veclist) varlist))))

;; explicate-control : Lif -> Cif , (We are generating some blocks which are not visited by any other blocks)
(define (explicate-control p)
  (set! vector-list '())
  (match p
    [(ProgramDefs info defs) 
      (define new-defs (for/list ([d defs]) 
        (match d
        ; [(Def label paramtypes returntype info e)
        [(Def fun param* rt info body)
          (set! basic-blocks (list))
          (define new-fun (string->symbol (string-append (symbol->string fun) "start")))
          ; (define-values (c3t let-binds) (explicate-tail e fun))
          (define-values (tail-exp var-list) (explicate-tail body))
          ; (printf "\n Basic blocks for ~a are ~a\n" new-fun basic-blocks)
          (define exp-dict (dict-set basic-blocks new-fun tail-exp))
          ; (set! localvars (append localvars let-binds))
          (define locals (set->list (list->set var-list)))
          (set! vector-list (make-vector-list (set->list (list->set vector-list)) var-list))
          (define new-info (dict-set '() 'locals locals))
          (define new-dict (dict-set new-info 'cfg (make-graph exp-dict new-fun)))
          ; (printf "locals are ~a" locals)
          (Def fun param* rt new-dict exp-dict)])))
          
      (ProgramDefs info new-defs)]

    [_ (error "Error: Unidentified case in explicate-control")]))


;; Remove empty edges
(define (remove-empty-edge edges)
  (if (null? edges)
      (list)
      (match (car edges)
        [(list a b) (cons (car edges) (remove-empty-edge (cdr edges)))]
        [_ (remove-empty-edge (cdr edges))])))

;; Remove redundant edges
(define (remove-redundant-edges edges) (set->list (list->set edges)))

(define (handle-tail tail)
  (match tail
    [(Seq stmt tail)
      (handle-tail tail)]
    [(Goto label) tail]
    [(IfStmt cnd (Goto label1) (Goto label2)) tail]
    [(Return es) tail]
    [(TailCall fn arg) tail]
    [_ (error "Error: Unidentified Case in handle-tail")]))


;; Handle each basic block
(define (handle-pair pair)
  (define block-label (car pair))
  (define last-stmt (handle-tail (cdr pair)))
  (match last-stmt
    [(Return x) (list (list))]   ;; IMPORTANT -> there might not any edges in the graph, but there can be vertices
    [(Goto next-label) (list (list block-label next-label))]
    [(IfStmt cnd (Goto thn-label) (Goto els-label)) (list (list block-label thn-label) (list block-label els-label))]
    [(TailCall fn arg) (list (list))]
    [_ (error "Error: Unidentified case in handle-pair")]))

;; Create the Control-Flow-Graph for basic blocks
(define (create-graph blocks)
  (if (null? blocks)
      (list)
      (append (handle-pair (car blocks)) (create-graph (cdr blocks)))))

;; Make the graph using multi-graph for basic blocks
(define (make-graph exp-dict new-fun)
  (define edges (create-graph exp-dict))
  (define correct-edges (remove-redundant-edges (remove-empty-edge edges)))
  (define graph (make-multigraph correct-edges))
  (if (null? correct-edges)
      (add-vertex! graph new-fun)
      10)
  graph)
  
  
;; Convert (Int n) --> (Imm n) and #t -> 1, #f -> 0, so as to follow the X86 grammar
(define (C->X86 exp)
  (match exp
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Void) (Imm 0)]
    [(Bool b)
     (match b
       [#t (Imm 1)]
       [#f (Imm 0)])]))

;; Return correct string for the operator
(define (op->str op)
  (match op
    ['> 'g]
    ['< 'l]
    ['>= 'ge]
    ['<= 'le]
    ['eq? 'e]
    [_ (error "Error: Unidentified case for op->str")]))


(define (list->number ls)
   (if (not (empty? ls))
        (if (not (equal? 1 (car ls)))
          (list->number (cdr ls))
          (+ (list->number (cdr ls)) (expt 2 (length (cdr ls)))))
        0))

;; type->binary : Type -> BinaryList
(define (type->binary tp)
    (if (not (empty? tp))
        (if (and (list? (car tp)) (equal? (car (car tp)) 'Vector))
            (cons 1 (type->binary (cdr tp)))
            (cons 0 (type->binary (cdr tp))))
        '()))

(define (get-tag len T)
  (let* ([type-num (arithmetic-shift (list->number (reverse (type->binary (cdr T)))) 7)]
         [type-len (bitwise-ior (arithmetic-shift len 1) 1)]
         [res (bitwise-ior type-num type-len)])
    res))

(define (place-args-in-regs args curr)
  (if (empty? args)
      empty
      (cons (Instr 'movq (list (C->X86 (car args))
                               (Reg (list-ref '(rdi rsi rdx rcx r8 r9) curr))))
            (place-args-in-regs (cdr args) (+ 1 curr)))))

(define (place-regs-in-args args curr)
  (if (empty? args)
      empty
      (cons (Instr 'movq (list (Reg (list-ref '(rdi rsi rdx rcx r8 r9) curr))
                               (C->X86 (car args))))
            (place-regs-in-args (cdr args) (+ 1 curr)))))


;; select for expression (which are assignment statements, as it is the output of explicate control)
(define (select-exp exp var)
  (match exp
    [(Int int)
     (list
      (Instr 'movq (list (Imm int) var)))]
    [(Bool b)
     (list
      (Instr 'movq (list (C->X86 (Bool b)) var)))]
    [(Void)
     (list
      (Instr 'movq (list (C->X86 (Void)) var)))]
    [(Var x)
        (cond 
        [(member x vector-list) (set! vector-list (append vector-list (list var)))])
     (list
      (Instr 'movq (list (Var x) var)))]
    [(Prim 'read '())
     (list
      (Callq 'read_int 0)
      (Instr 'movq (list (Reg 'rax) var)))]
    [(Prim '- (list a))
     (list
      (Instr 'movq (list (C->X86 a) var))
      (Instr 'negq (list var)))]
    [(Prim '+ (list a1 a2))
     (list
      (Instr 'movq (list (C->X86 a1) var))
      (Instr 'addq (list (C->X86 a2) var)))]
    [(Prim '- (list a1 a2))
     (list
      (Instr 'movq (list (C->X86 a1) var))
      (Instr 'subq (list (C->X86 a2) var)))]
    [(Prim 'not (list a1))
     (list
      (Instr 'movq (list (C->X86 a1) var))
      (Instr 'xorq (list (Imm 1) var)))]
    [(Prim 'vector-ref (list a (Int n)))
      (list (Instr 'movq (list (C->X86 a) (Reg 'r11))) 
            (Instr 'movq (list (Deref 'r11 (* 8 (+ 1 n))) var)))]
    [(Prim 'vector-length (list a))
      (list (Instr 'movq (list (C->X86 a) (Reg 'r11))) 
            (Instr 'movq (list (Deref 'r11 0) var))
            (Instr 'sarq (list (Imm 1) var))
            (Instr 'andq (list (Imm 63) var)))]
    [(Prim 'vector-set! (list atm1 (Int n) atm2))
    (list (Instr 'movq (list (C->X86 atm1) (Reg 'r11)))
          (Instr 'movq (list (C->X86 atm2) (Deref 'r11 (* 8 (+ 1 n)))))
          (Instr 'movq (list (Imm 0) var)))]
    [(Prim op (list a1 a2)) #:when (or (eq? op '>) (eq? op '<) (eq? op '>=) (eq? op '<=) (eq? op 'eq?))
     (list
      (Instr 'cmpq (list (C->X86 a2) (C->X86 a1)))  ;; IMPORTANT -> the order of evaluation is backward for 'cmpq (Wasted a lot of time debugging this)
      (Instr 'set (list (op->str op) (Reg 'al)))
      (Instr 'movzbq (list (Reg 'al) var)))]
    [(Allocate len T)
            (let ([tag (get-tag len T)]) ;; need to actually calculate tag using bitwise stuff
              (list (Instr 'movq (list (Global 'free_ptr) var))
                    (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
                    (Instr 'movq (list var (Reg 'r11)))
                    (Instr 'movq (list (Imm tag) (Deref 'r11 0)))))] ;; deref r11 at 0 always?
    [(GlobalValue name) (list (Instr 'movq (list (Global name) var)))]
    [(FunRef fn) (list (Instr 'leaq (list (FunRef fn) var)))]
    [(Call fn args) 
      (append (place-args-in-regs args 0)
        (list (IndirectCallq (C->X86 fn) (length args)) 
            (Instr 'movq (list (Reg 'rax) var))))]
    [_    ;(printf "\nMatching ~a\n" exp)
        (error "Error: Unidentified Case in select-exp")]))

;; select for statement, this function handles the special case when one of
;; the rhs of assignment is same as lhs variable. (We missed one case here for unary subtraction (negation))
;; Another mistake was that we did not return a list for special cases
(define (select-statement exp)
  (match exp
    [(Assign (Var var) (Prim op (list (Var y) a2))) #:when (or (eq? op '+) (eq? op '-))  ;; Takes care of +, - (binary)
     (cond
       [(equal? var y)
        (if (eq? op '+)
            (list (Instr 'addq (list (C->X86 a2) (Var var))))
            (list (Instr 'subq (list (C->X86 a2) (Var var)))))]
       [else
        (select-exp (Prim op (list (Var y) a2)) (Var var))])]
    [(Assign (Var var) (Prim op (list a1 (Var y)))) #:when (or (eq? op '+) (eq? op '-))  ;; Takes care of +, - (binary)
     (cond
       [(equal? var y)
        (if (eq? op '+)
            (list (Instr 'addq (list (C->X86 a1) (Var var))))
            (list
             (Instr 'negq (list (Var var)))
             (Instr 'addq (list (C->X86 a1) (Var var)))))]
       [else
        (select-exp (Prim op (list a1 (Var y))) (Var var))])]
    [(Assign (Var var) (Prim '- (list (Var y))))  ;; Takes care of - (unary)
     (if (equal? var y)
         (list (Instr 'negq (list (Var y))))
         (select-exp (Prim '- (list (Var y))) (Var var)))]
    [(Assign (Var var) (Prim 'not (list (Var y))))
     (if (equal? var y)
         (list (Instr 'xorq (list (Imm 1) var)))
         (select-exp (Prim 'not (list (Var y))) (Var var)))]
    [(Assign (Var var) es) (select-exp es (Var var))]
    [(Prim 'read (list))
     (list (Callq 'read_int 0))]                ;; Read is now allowed as a statement
    [(Collect n) (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                       (Instr 'movq (list (Imm n) (Reg 'rsi))) ;; seems right
                       (Callq 'collect 0))]                  
    [_ (error "Error: Unidentified Case in select-statement")]))

;; select for tail (Refer the grammar of C_var for tail)
(define (select-tail exp fun)
  (match exp
    [(Seq stmt tail)
     (append
      (select-statement stmt)
      (select-tail tail fun))]
    [(Goto label)
     (list (Jmp label))]
    [(IfStmt (Prim 'vector-ref (list v (Int i) 'Integer)) (Goto label1) (Goto label2))
      (let ([v_ (C->X86 v)])
      (list
	      (Instr 'movq (list v_ (Reg 'r11)))
        (Instr 'cmpq (list (Imm 1) (Deref 'r11 (* 8 (add1 i)))))
        (JmpIf 'e label1)
        (Jmp label2)))]
    [(IfStmt (Prim op (list e1 e2)) (Goto label1) (Goto label2))
     (list
      (Instr 'cmpq (list (C->X86 e2) (C->X86 e1))) ;; IMPORTANT -> the order of evaluation is backward for 'cmpq
      (JmpIf (op->str op) label1)
      (Jmp label2))]
    [(Return (Prim 'read '()))
     (list
      (Callq 'read_int 0)
      (Jmp 'conclusion))]
    [(Return es)
     (append
      (select-exp es (Reg 'rax))
      (list (Jmp (string->symbol (string-append (symbol->string fun) "conclusion")))))]
    [(TailCall fn args) 
      (append 
        (place-args-in-regs args 0)
        (list 
          (TailJmp (C->X86 fn) (length args))))]
    [(HasType tail type) (select-tail tail fun)]
    
    [_ (error "Error: Unidentified Case in select-tail")]))

;; Align the frame to be a multiple of 16
(define (align-16 len)
  (if (odd? len)
      (* (+ len 1) 8)
      (* len 8)))

;; Give stack-size (It must be a multiple of 16)
(define (give-st-size var-list)
  (define len (length var-list))
  (align-16 len))

;; generate blocks for each label in C_if
(define (generate-blocks exp-dict)
  (define listOfBlock (for/list ([pair exp-dict]) (Block '() (select-tail (cdr pair)))))
  (define listOfLabel (for/list ([pair exp-dict]) (car pair)))
  (define block-dict (list))
  (for/list ([block listOfBlock] [label listOfLabel]) (cons label block)))

;; select-instructions : C_if -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info exp-dict)
        (printf "\nInfo- ~a\n" info)
       (define new-info (dict-set info 'stack-size (give-st-size (cdr (car info)))))
       (set! vector-list (set->list (list->set vector-list)))
        (printf "\nvector-list ~a\n" vector-list)
       (X86Program new-info (generate-blocks exp-dict))]

    [(ProgramDefs info defs)
     (define new-defs (for/list ([d defs])
                      (match d
                        [(Def label paramtypes returntype info alist)
                         (define args (for/list ([param paramtypes])
                                        (match param
                                          [`(,v : ,t)
                                           (Var v)])))
                         (define new-alist (for/list ([p alist])
                            (cons (car p) (Block '() (if (equal? (car p) (string->symbol (string-append (symbol->string label) "start")))
                            (append (place-regs-in-args args 0) (select-tail (cdr p) label))
                            (select-tail (cdr p) label))))))
                         (Def label '() returntype
                              (dict-set info 'num-params (length paramtypes))
                              new-alist)])))
      (set! vector-list (set->list (list->set vector-list)))
     (ProgramDefs info new-defs)]
    [_ (error "Error: Unidentified Case in select-instructions")]))


;; change a variable into the Deref struct
(define (handle-arg arg mapping)
  (match arg
    [(Var x)
     (Deref 'rbp (dict-ref mapping x))]
    [_ arg]))

;; Replaces the variables with stack location with respect to rbp (base-pointer)
(define (single-instr instr mapping)
  (match instr
    [(Instr op (list a1 a2))  ;; Handles movq and addq
     (Instr op (list (handle-arg a1 mapping) (handle-arg a2 mapping)))]
    [(Instr 'popq (list a))   ;; Handles popq
     instr]
    [(Instr op (list a))      ;; Handles pushq and negq
     (Instr op (list (handle-arg a mapping)))]
    [_ instr]))               ;; Handles callq, Jmp, Retq

;; helper for assign-homes
(define (assign-home-helper instr mapping)
  (if (null? instr)
      (list)
      (cons (single-instr (car instr) mapping) (assign-home-helper (cdr instr) mapping))))


;; creates a mapping from variable names to integers (Which are the offset fromt the rbp register)
(define (create-mapping var-list index)
  (if (null? var-list)
      (list)
      (dict-set (create-mapping (cdr var-list) (+ 1 index)) (car var-list) (* index -8))))


;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info exp)
     (define block (dict-ref exp 'start))
     (match block
       [(Block block-info instr)
        (define mapping (create-mapping (dict-ref info 'locals) 1))
        (define new-block (Block block-info (assign-home-helper instr mapping)))
        (define new-exp (dict-set '() 'start new-block))
        (X86Program info new-exp)]
       [_ (error "Error: Unidentified Case while matching block")])]
    [_ (error "Error: Unidentified Case while matching program after select instruction pass")]))


;; checks if an expression is Integer
(define (int? exp)
  (match exp
    [(Int n) #t]
    [_ #f]))

;; partially evaluate an expression in L_var
(define (pe-exp-lvar env  exp)
  (match exp
    [(Var x)
     (define value (dict-ref env x))
     (cond
       [(int? value) value]
       [else (Var x)])]
    [(Let x e body)
     (define new-exp (pe-exp-lvar env e))
     (define new-env (dict-set env x new-exp))
     (define body-result (pe-exp-lvar new-env body))
     (cond
       [(int? body-result) body-result]
       [(int? new-exp) body-result]
       [else (Let x new-exp body-result)])]
    [(Int n)
     (Int n)]
    [(Prim 'read '())
     (Prim 'read '())]
    [(Prim '- (list e1))
     (pe-neg (pe-exp-lvar env e1))]
    [(Prim '+ (list e1 e2))
     (pe-add (pe-exp-lvar env e1) (pe-exp-lvar env e2))]
    [_ (error "Error: Unidentified Case")]))

;; Partial-evaluator for L_var
(define (partial-lvar p)
  (match p
    [(Program info exp)
     (Program info (pe-exp-lvar '() exp))]
    [_ (error "Error: Unidentified Case")]))

;; process addition on residual form
(define (opt-pe-add e1 e2)
  (match* (e1 e2)
    [((Int n1) (Int n2))
     (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) inert)))
     (Prim '+ (list (Int (fx+ n1 n2)) inert))]
    [((Prim '+ (list (Int n1) inert)) (Int n2))
     (Prim '+ (list (Int (fx+ n1 n2)) inert))]
    [((Prim '+ (list (Int n1) inert1)) (Prim '+ (list (Int n2) inert2)))
     (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list inert1 inert2))))]
    [(_ _) (Prim '+ (list e1 e2))]))
    

;; partially evaluate an expression to the 'Residual' form of expression (Refer page 34).
(define (opt-pe-exp-lvar env exp)
  (match exp
    [(Var x)
     (define value (dict-ref env x))
     (cond
       [(int? value) value]
       [else (Var x)])]
    [(Int n)
     (Int n)]
    [(Prim 'read '())
     (Prim 'read '())]
    [(Prim '- (list e1))
     (pe-neg (opt-pe-exp-lvar env e1))]
    [(Prim '+ (list e1 e2))
     (opt-pe-add (opt-pe-exp-lvar env e1) (opt-pe-exp-lvar env e2))]
    [(Let x e body)
     (define new-exp (opt-pe-exp-lvar env e))
     (define new-env (dict-set env x new-exp))
     (define body-result (opt-pe-exp-lvar new-env body))
     (cond
       [(int? body-result) body-result]
       [(int? new-exp) body-result]
       [else (Let x new-exp body-result)])]
    [_ (error "Error: Unidentified Case while matching expression for optimised partial evaluator")]))

;; Optimized partial-evaluator for L_var
(define (opt-par-lvar p)
  (match p
    [(Program info exp)
     (Program info (opt-pe-exp-lvar '() exp))]
    [_ (error "Error: Unidentified Case while matching program for optimised partial evaluator")]))

;; (set v ....) -> creates a set with specified values, similary there are other functions like
;; (set-union set1 set2), (set-subtract set1 set2), (set-member? set1 v), (set-count set1), (set->list set1)

;; Finds the arguments which are in read set of an instruction
(define (read-set instr)
  (match instr
    [(Instr 'movq (list a b))
     (match a
       [(Imm x) (set)]
       [_ (set a)])]
    [(Instr 'addq (list a b))
     (match a
       [(Imm x) (set b)]
       [_ (set a b)])]
    [(Instr 'negq (list a))
     (set a)]
    [(Instr 'popq (list a))
     (set)]
    [(Instr 'pushq (list a))
     (set a)]
    [(Instr 'xorq (list a b))
     (match a
       [(Imm x) (set b)]
       [_ (set b)])]
    [(Instr 'cmpq (list a b))
     (match a
       [(Imm x) (match b [(Imm y) (set)] [_ (set b)])]
       [_ (match b [(Imm y) (set a)] [_ (set a b)])])]
    [(Instr 'set (list a b))
     (set)]
    [(Instr 'movzbq (list a b))
     (set (Reg 'rax))] ;; NEED TO CONFIRM THIS ! (whether to use %al or %rax)
    [(JmpIf cc label)
     (set)]
    [(Callq label arity)
     (list->set (take '(rdi rsi rdx rcx r8 r9) arity))]  ;; for now we return an empty set, but if arity > 0, then we need to return the register used for parameter passing
    [(IndirectCallq label arity)
     (list->set (take '(rdi rsi rdx rcx r8 r9) arity))]
    [(TailJmp label arity)
     (list->set (take '(rdi rsi rdx rcx r8 r9) arity))]
    [(Jmp 'conclusion) (set (Reg 'rax) (Reg 'rsp))] ;; We can hard-core this because we know conclusion block reads from rax and rsp
    [(Retq)
     (set (Reg 'rax))]  ;; Check this, I am not sure if it is correct, but the logic here is that
                        ;; when we return from a function, rax will be read by the caller.
    [_ (set)]))  ;; for everything else we return empty set

(define caller-saved (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))
(define callee-saved (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))

;; Finds the arguments which are in the write set of instruction 
(define (write-set instr)
  (match instr
    [(Instr 'movq (list a b))
     (set b)]
    [(Instr 'addq (list a b))
     (set b)]
    [(Instr 'negq (list a))
     (set a)]
    [(Instr 'popq (list a))
     (set a)]
    [(Instr 'pushq (list a))
     (set)]
    [(Instr 'xorq (list a b))
     (set b)]
    [(Instr 'cmpq (list a b))
     (set)]
    [(Instr 'set (list a b))    ;; Only the second argument will be written into
     (set b)]
    [(Instr 'movzbq (list a b))
     (set b)]
    [(JmpIf cc label)
     (set)]
    [(Callq 'collect arity)
     (list->set vector-list)]   ;; Tuple type variables are to be spilled during call to collector - Pg 111
    [(Callq label arity)
     (list->set caller-saved)]  ;; All the caller-saved registers are in the write set as mentioned on Page 36.
    [(IndirectCallq label arity)
     (list->set caller-saved)]
    [(Retq) (set)]
    [_ (set)]))
  
;; dictionary mapping labels to the live-before set of the blocks
(define label->live (list))
(define bdict (list))

;; Takes a X86 instruction and live-before set and gives the live after set
(define (live-before-op instr live-before)
  ;(printf "Live before is a ~a\n" live-before)
  (set-union (set-subtract (list->set live-before) (write-set instr)) (read-set instr)))
  
;; Takes a list of instructions and compute the live after sets, (list of sets)
(define (live-before instrs live-before-set)
  (match instrs
    [(list) (list)]
    [_
     (define new-set (live-before-op (car instrs) live-before-set))
     (cons new-set (live-before (cdr instrs) new-set))]))

;; Process blocks -> returns a list of (label . block)
(define (uncover-blocks tsort-order block-dict)
  (match tsort-order
    [(list) (list)]
    [_
     (define curr-label (car tsort-order))
     (define block (dict-ref block-dict curr-label))
     (match block
       [(Block b-info instrs)
        (define last-instr (last instrs))
        (define second-last-instr (if (< 1 (length instrs)) (cadr (reverse instrs)) (Retq))) ;; Adding (Retq) so that the default case matches for second-last-instr
        (define live-before-set (match last-instr
                      [(Retq) (set)]
                      [_
                       (define other-label (match last-instr [(Jmp lab) lab] [_ (error "The last instruction in X86 is incorrect")]))
                       (define live-vars (dict-ref label->live other-label))
                       (match second-last-instr
                         [(JmpIf cc next-label) (set-union (dict-ref label->live next-label) live-vars)]
                         [_ live-vars])]))
                        
        (define live-before-list (reverse (live-before (reverse instrs) live-before-set))) ;; give live-before-set as input
        (set! label->live (cons (cons curr-label (car live-before-list)) label->live))
        (define new-info (dict-set b-info 'live-before live-before-list))
        (define new-block (Block new-info instrs))
        (cons (cons curr-label new-block) (uncover-blocks (cdr tsort-order) block-dict))]
       [_ (error "Unidentified case in uncover-blocks")])]))



(define (analyze-single-block curr-label live-before-of-successors) 
     (define block (dict-ref bdict curr-label))
     (match block
       [(Block b-info instrs)                  
        (define live-before-list (reverse (live-before (reverse instrs) live-before-of-successors))) ;; give live-before-set as input])))
        ; (set! label->live (cons (cons curr-label (car live-before-list)) label->live))
        (define new-info (dict-set b-info 'live-before live-before-list))
        (define new-block (Block new-info instrs))
        (set! bdict (dict-set bdict curr-label new-block))
        (car live-before-list)]))

;; Dataflow Analysis
(define (analyze-dataflow G transfer bottom join)
  (for ([v (in-vertices G)])
    (set! label->live (cons (cons v bottom) label->live)))   ;; At the start ever block's live before set will be empty (bottom --> empty set)
    
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))          ;; Put all the nodes in the queue
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom]) ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref label->live pred))))
         (define output (transfer node input))  ;; block and the union of live-before set of all successor blocks
          
         (cond [(not (equal? output (dict-ref label->live node))) ;; If the live-before is different from previous iteration
                (set! label->live (dict-set label->live node output))
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))                   ;; then put the neighbors in the queue

  label->live)  ;; Return the mapping of every block with it's live before set (And it also finds the live variables for all instrs)


;; Uncover-live pass
(define (uncover-live-pass p)
  (match p
    [(ProgramDefs info defs)
      (set! label->live (list (cons 'conclusion (set (Reg 'rax) (Reg 'rsp)))))  ;; We add this because there is no entry for conclusion in our basic-blocks dict
      (define new-defs (for/list ([d defs]) (match d
        [(Def label paramtypes rt info blocks)
          (define cfg (dict-ref info 'cfg))
          (define t-cfg (transpose cfg))
          (set! bdict blocks)
          (define label-block-mapping (analyze-dataflow t-cfg analyze-single-block (set) set-union))
        (Def label paramtypes rt info bdict)])))
     (ProgramDefs info new-defs)]

    [_ (error "Error: Unidentified Case while matching X86Program in uncover-live-pass")]))

;; Process single instruction, returns list of edges, where an edge is a list of two elements, source and vertex
(define (generate-edges instr live-after-set locals)
  (match instr
    [(Instr 'movq (list a b))
     (map (lambda (x) (if (or (equal? x a) (equal? x b)) (list) (list b x))) (set->list live-after-set))]
    [(Instr 'movzbq (list a b))
     (map (lambda (x) (if (or (equal? x (Reg 'rax)) (equal? x b)) (list) (list b x))) (set->list live-after-set))] ;; CHECK IF THIS IS CORRECT !!
    [(IndirectCallq label arity)
      (define vecs (set->list (set-intersect (list->set vector-list) (list->set locals))))
      (define edges '())
      (display vecs)
      (for ([v live-after-set])
         (for ([u caller-saved])
           (if (equal? v u)
               (verbose "skip self edge on" v)
               (set! edges (append edges (list (list u v))))))
         (for ([u callee-saved])
           (if (or (equal? v u) (not (member v vecs)))
               (verbose "skip self edge or non-vector on" v)
               (set! edges (append edges (list (list u v)))))))
        edges
      ]
    [(Callq label arity)
      (define vecs (set->list (set-intersect (list->set vector-list) (list->set locals))))
      (define edges '())

      (for ([v live-after-set])
         (for ([u caller-saved])
           (if (equal? v u)
               (verbose "skip self edge on" v)
               (set! edges (append edges (list (list u v))))))
         (for ([u callee-saved])
           (if (or (equal? v u) (not (member v vecs)))
               (verbose "skip self edge or non-vector on" v)
               (set! edges (append edges (list (list u v)))))))
        edges
      ]
    [_
     (define write-sett (write-set instr))
     (map (lambda (x) (if (equal? (car x) (cadr x)) (list) x)) (cartesian-product (set->list write-sett) (set->list live-after-set)))]
    ))

    
;; Process list of instructions
(define (build-graph-exp instrs live-after locals)
  (match instrs
    [(list a) (list)]
    [_
     (append
      (generate-edges (car instrs) (car live-after) locals)
      (build-graph-exp (cdr instrs) (cdr live-after) locals))]))

;; Build the graph for each block
(define (build-graph-block block locals)
  (match block
    [(Block b-info instrs)
     (define live-bef (dict-ref b-info 'live-before))
     (define edges (build-graph-exp instrs (cdr live-bef) locals))
     (remove-redundant-edges (remove-empty-edge edges))]
    [_ (error "Error : Unidentified Case while matching block in build-graph-block")]))

;; Build interference graph
(define (build-graph p)
  (match p
    [(ProgramDefs info defs)
      (define new-defs (for/list ([d defs]) (match d
        [(Def label paramtypes rt info blocks)
        (define locals (dict-ref info 'locals))
        (define edge-list (foldl append (list) (for/list ([block-pair blocks]) (build-graph-block (dict-ref blocks (car block-pair)) locals))))
        (define correct-edges  (remove-redundant-edges (remove-empty-edge edge-list)))
        (printf (graphviz (undirected-graph correct-edges)))
        (Def label paramtypes rt (dict-set info 'conflict (undirected-graph correct-edges)) blocks)])))
     (ProgramDefs info new-defs)]
    [_ (error "Error: Unidentified Case while matching X86Program in build-graph pass")]))

;; Creates a dictionary where every node is mapped to -1 (which indicates not visited)
(define (make-colors nodes dict)
    (match nodes
      ['() dict]
      [_
       (match (car nodes)  ;; Checks if the first character is % (indicating that it is a register)
         [(Reg r) (make-colors (cdr nodes) (dict-set dict (car nodes) -2))]
         [_ (make-colors (cdr nodes) (dict-set dict (car nodes) -1))])]))

;; Structure describing our node
(struct tup (name val))             
            (define tup->                         
            (lambda (tup1 tup2)                 
                (> (tup-val tup1) (tup-val tup2))))

;; find the smallest color which none of the neighbors has
(define (colour-node colour ncolours)
    (if (member colour ncolours) 
        (colour-node (+ 1 colour) ncolours)
        colour))

;; Update the saturation list of all the neighbors
(define (update-saturation saturation neighbours q colour)
    (match neighbours
        ['() saturation]
        [_ 
            (define node (car neighbours))
            (define node-sat (dict-ref saturation node))
            (cond 
                [(member colour node-sat) (update-saturation saturation (cdr neighbours) q colour)]
                [else 
                    (define new-sat (dict-set saturation node (append node-sat (list colour))))
                    (pqueue-push! q (tup node (length (dict-ref new-sat node))))
                    (update-saturation new-sat (cdr neighbours) q colour)])
            ]))

;; Greedy DSATUR algorithm
(define (dsatur q colours saturation graph)
    (cond
        [(eq? 0 (pqueue-count q)) colours]
        [else 
            (define node (pqueue-pop! q))
            (cond   ;add rax condition
                [(eq? (dict-ref colours (tup-name node)) -1) 
                    (define neighbors (sequence->list (in-neighbors graph (tup-name node)))) ;; get neighbours
                    (define ncolours (map (lambda (x) (dict-ref colours x)) neighbors))  ;; get neighbor colors
                    (define new-colour (colour-node 0 ncolours))  ;; get the color for current node
                    (define new-sat (update-saturation saturation neighbors q new-colour))
                    (define new-colours (dict-set colours (tup-name node) new-colour))
                    (dsatur q new-colours new-sat graph)]
                [else (dsatur q colours saturation graph)])]))

(define spill-st (list))
(define spill-root (list))
; (define register-list (list (Reg 'rbx)))
(define register-list (list (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

(define (add-stack-locations register-list num)
    (cond
        [(<= num 0) register-list]
        [else (add-stack-locations (append register-list (list (Deref 'rbp (* -8 num)))) (- num 1))]))
        
(define (generate-colourreg mapping num reg-list)
    (match reg-list
        ['() mapping]
        [_ (generate-colourreg (append mapping (list (cons num (car reg-list)))) (+ num 1) (cdr reg-list))]))

;; Replace a single variable with stack-location or register
(define (allocate-handle-arg arg colouring colourreg offset)
  (match arg
    [(Var x)
        (define col (dict-ref colouring (Var x)))
        (cond
            [(< col (length register-list)) (list-ref register-list col)]
            [(member x vector-list) 
                (define loc (* 8 (+ 1 (- col (+ 1 (length register-list))))))
                (set! spill-root (append spill-root (list loc)))
                (Deref 'r15 loc)]
            [else 
                (define loc (* -8 (- col (+ 1 (length register-list)))))
                (set! spill-st (append spill-st (list loc)))
                (Deref 'rbp (- loc 32))])]
    [_ arg]))

;; Replaces the variables with stack location with respect to rbp (base-pointer)
(define (allocate-single-instr instr colouring colourreg offset)
  (match instr
    [(Instr op (list a1 a2))  ;; Handles movq and addq
     (Instr op (list (allocate-handle-arg a1 colouring colourreg offset) (allocate-handle-arg a2 colouring colourreg offset)))]
    [(Instr 'popq (list a))   ;; Handles popq
     instr]
    [(Instr op (list a))      ;; Handles pushq and negq
     (Instr op (list (allocate-handle-arg a colouring colourreg offset)))]
    [_ instr]))               ;; Handles callq, Jmp, Retq

;; Replaces each variable with the register or stack location
(define (allocate-register-helper instr colouring colourreg offset)
  (if (null? instr)
      (list)
      (cons (allocate-single-instr (car instr) colouring colourreg offset) (allocate-register-helper (cdr instr) colouring colourreg offset))))

;; create a mapping for every variable in our program to a Stack-location or a Register
(define (allocate-create-mapping nodes colouring colorReg)
  (if (null? nodes)
      (list)
      (match (car nodes)
        [(Reg r) (allocate-create-mapping (cdr nodes) colouring colorReg)]
        [_ (cons (cons (car nodes) (dict-ref colorReg (dict-ref colouring (car nodes)))) (allocate-create-mapping (cdr nodes) colouring colorReg))])))

;; finds all the callee-saved register being used in the program
(define (used-callee allocation)
  (match allocation
    ['() (list)]
    [_
     (match (car allocation)
       [(Reg r)
        (if (member (Reg r) callee-saved)
            (cons (Reg r) (used-callee (cdr allocation)))
            (used-callee (cdr allocation)))]
       [_ (used-callee (cdr allocation))])]))

;; Handles each of the block and generates a new corresponding block
(define (new-allocation block colouring colourreg offset)
  (match block
    [(Block info instrs) (Block info (allocate-register-helper instrs colouring colourreg offset))]
    [_ (error "Error: unidentified case in new-allocation" block)]))

;; Replaces variable names with registers or stack locations
(define (allocate-registers p)
    (match p
        [(X86Program info exp)
            (define graph (dict-ref info 'conflict))
            (define nodes (sequence->list (in-vertices graph)))
            
            ; create the priority queue by passing in the comparator
            (define q (make-pqueue tup->))
            (for ([i nodes])
              (pqueue-push! q (tup i (sequence-length (in-neighbors graph i)))))
            ; Mapping between nodes and it's saturation list
            (define saturation (map (lambda (x) (cons x (list))) nodes))
            ; Initially every Variable is assigned -1 as the color and -2 for the Registers
            (define colours (make-colors nodes '()))
            
            (define colouring (dsatur q colours saturation graph))
            (define color-list (remove-duplicates (dict-values colouring)))
        
            (define spilled-vars (let ([x (- (- (length color-list) 1) (length register-list))]) (if (> 0 x) 0 x))) 
  
            (define new-reg-list (add-stack-locations register-list spilled-vars))
            (define colourreg (generate-colourreg '() 0 new-reg-list))
                    
            (define mapping (allocate-create-mapping nodes colouring colourreg))
            
            (define callee-reg (remove-duplicates (used-callee (dict-values mapping))))
            (define n-info (dict-set info 'used_callee callee-reg))
            (define new-info (dict-set n-info 'spilled-vars spilled-vars))
            (set! spill-root (set->list (list->set spill-root)))
            (define n-new-info (dict-set new-info 'num-root-spills (length spill-root)))
            (define new-exp (for/list ([block-pair exp]) (cons (car block-pair) (new-allocation (dict-ref exp (car block-pair)) colouring colourreg (* 8 (length callee-reg))))))
            ;(define new-block (Block block-info (allocate-register-helper instr mapping (* 8 (length callee-reg)))))
            ;(define new-exp (dict-set '() 'start new-block))
            (X86Program n-new-info new-exp)]
        [_ (error "Error: Unidentified Case while matching program in allocate registers pass")]))


;; Handles transformation of single instruction
(define (patch-one-instr instr)
  (match instr
    [(Instr op (list (Reg r1) (Reg r2)))
     (cond
       [(equal? r1 r2) (list)]
       [else (list instr)])]
    [(Instr op (list (Deref 'rbp int1) (Deref 'rbp int2)))
     (cond
       [(equal? int1 int2) (list)]
       [else (list
              (Instr 'movq (list (Deref 'rbp int1) (Reg 'rax)))
              (Instr op (list (Reg 'rax) (Deref 'rbp int2))))])]
    [(Instr op (list (Deref 'r15 int1) (Deref 'r15 int2)))
     (cond
       [(equal? int1 int2) (list)]
       [else (list
              (Instr 'movq (list (Deref 'r15 int1) (Reg 'rax)))
              (Instr op (list (Reg 'rax) (Deref 'r15 int2))))])]
    [(Instr op (list (Deref 'r15 int1) (Deref 'rbp int2)))
        (list
            (Instr 'movq (list (Deref 'r15 int1) (Reg 'rax)))
            (Instr op (list (Reg 'rax) (Deref 'rbp int2))))]
    [(Instr op (list (Deref 'rbp int1) (Deref 'r15 int2)))
        (list
            (Instr 'movq (list (Deref 'rbp int1) (Reg 'rax)))
            (Instr op (list (Reg 'rax) (Deref 'r15 int2))))]
    [(Instr 'cmpq (list  arg1 (Imm n)))
     (list
      (Instr 'movq (list (Imm n) (Reg 'rax)))
      (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [(Instr 'movzbq (list  arg1 (Imm n)))
     (list
      (Instr 'movq (list (Imm n) (Reg 'rax)))
      (Instr 'mvzbq (list arg1 (Reg 'rax))))]
    [(Instr op (list e1 e2)) 
     (match (list e1 e2)
       [(list (Global name) (Deref a b)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                               (Instr op (list (Reg 'rax) e2)))]
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                             (Instr op (list (Reg 'rax) e2)))]
       [(list (Global name) (Global name1)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                                  (Instr op (list (Reg 'rax) e2)))]
       [(list (Deref a b) (Global name)) (list (Instr 'movq (list e1 (Reg 'rax)))
                                               (Instr op (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr op (list e1 e2)))])]
    [_ (list instr)]))

;; changes movq and addq with two stack locations as the arguments, since in X86 only 1 memory reference
;; per instruction is allowed
(define (patch-helper instrs)
  (if (null? instrs)
      (list)
      (append (patch-one-instr (car instrs)) (patch-helper (cdr instrs)))))

;; patch block helper
(define (patch-block-helper block)
  (match block
    [(Block info instrs) (Block info (patch-helper instrs))]
    [_ (error "Error: Unidentified Case in patch-block-helper")]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info exp)
     (define new-exp (for/list ([block-pair exp]) (cons (car block-pair) (patch-block-helper (dict-ref exp (car block-pair))))))
     (X86Program info new-exp)]
    [_ (error "Error: Unidentified Case")]))


;; generates the Conclusion
(define (conclusion-gen stack-size used-callee roots)
  (append
   (list
    (Instr 'subq (list (Imm (* 8 roots)) (Reg 'r15)))
    (Instr 'addq (list (Imm stack-size) (Reg 'rsp))))
   (for/list ([reg (reverse used-callee)]) (Instr 'popq (list reg)))  ;; POP in the reverse direction, the register which was pushed last should be popped first
   (list
    (Instr 'popq (list (Reg 'rbp)))
    (Retq)))
  )

;; generates Main block
(define (main-gen stack-size used-callee roots)
  (append
   (list
    (Instr 'pushq (list (Reg 'rbp)))
    (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
   (for/list ([reg used-callee]) (Instr 'pushq (list reg)))
   (list
    (Instr 'subq (list (Imm stack-size) (Reg 'rsp)))
    (Instr 'movq (list (Imm 16384) (Reg 'rdi)))
    (Instr 'movq (list (Imm 16384) (Reg 'rsi)))
    (Callq 'initialize 0)
    (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
    (for/list ([i roots]) (Instr 'movq (list (Imm 0) (Deref 'r15 (* i 8)))))
    (list
        (Instr 'addq (list (Imm (* 8 roots)) (Reg 'r15)))
        (Jmp 'start))))


;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info exp) 
    (define roots (dict-ref info 'num-root-spills))
    (define spilled (dict-ref info 'spilled-vars))
    (define used-callee (dict-ref info 'used_callee))
    (define st-size (- (align-16 (+ spilled (length used-callee))) (* 8 (length used-callee)))) ;; Refer the formula on Page 50
    (define main-block (Block '() (main-gen st-size used-callee roots)))
    (define conclusion-block (Block '() (conclusion-gen st-size used-callee roots)))
    (define new-exp (dict-set exp 'main main-block))
    (define final-exp (dict-set new-exp 'conclusion conclusion-block))
    (X86Program info final-exp)]
    [_ (error "Error: Unidentified Case")]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ;;("partial-evaluator" ,partial-lvar ,interp-Lvar)
     ;;("optimized-par-eval" ,opt-par-lvar ,interp-Lvar)
     ("shrink" ,shrink ,interp-Lfun)
     ("uniquify" ,uniquify ,interp-Lfun)
     ("reveal-function" ,reveal-function ,interp-Lfun-prime)
     ("limit-function" ,limit-function ,interp-Lfun-prime)
     ("uncover-get" ,uncover-get ,interp-Lfun-prime)
     ("expose-allocation" ,expose-allocation ,interp-Lfun-prime)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime)
     ("explicate control" ,explicate-control ,interp-Cfun)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
     ("uncover live" ,uncover-live-pass ,interp-pseudo-x86-3)
     ("build graph" ,build-graph ,interp-pseudo-x86-3)
     ;  ("assign homes" ,assign-homes ,interp-x86-0)
     ;("allocate-registers" ,allocate-registers ,interp-pseudo-x86-2)
     ;("patch instructions" ,patch-instructions ,interp-x86-2)
     ;("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-2)
     ))

