#lang racket
(require racket/set racket/stream)
(require racket/dict)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "interp-Lif.rkt")
(provide (all-defined-out))
(AST-output-syntax 'concrete-syntax)

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
    [(Var var) exp]
    [(If e1 e2 e3)
     (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [(Let x e body)
     (Let x (shrink-exp e) (shrink-exp body))]
    [(Prim 'and (list e1 e2))
     (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (shrink-exp e)))]
    [_ (error "Error: Unidentified Case in shrink-exp")]
    ))

;; Shrink : L_if -> L_if
(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]
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
      [(If e1 e2 e3)
       (define e1^ ((uniquify-exp env) e1))
       (define e2^ ((uniquify-exp env) e2))
       (define e3^ ((uniquify-exp env) e3))
       (If e1^ e2^ e3^)]
      [(Let x e body)
       (define rhs ((uniquify-exp env) e))
       (define new-name (gensym x))
       (define new-env (dict-set env x new-name))
       (Let new-name rhs ((uniquify-exp new-env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [_ (error "Error: Unidentified Case in uniquify-exp")])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]
    [_ (error "Error: Unidentified Case in uniquify")]))

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
       [(and (not (atom? e1)) (not (atom? e2)))
        (define new-name-1 (gensym "tmp"))
        (define new-name-2 (gensym "tmp"))
        (Let new-name-1 (rco_exp e1)
             (Let new-name-2 (rco_exp e2)
                  (Prim '+ (list (Var new-name-1) (Var new-name-2)))))]
       [(atom? e1)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e2)
             (Prim '+ (list e1 (Var new-name))))]
       [(atom? e2)
        (define new-name (gensym "tmp"))
        (Let new-name (rco_exp e1)
             (Prim '+ (list (Var new-name) e2)))]
       [else (error "Error: Unidentified Case")]
       )]
    [(Prim '- (list e1))
     (define new-name (gensym "tmp"))
     (Let new-name (rco_exp e1)
          (Prim '- (list (Var new-name))))]
    [else (error "Error: Unidentified Case")]))
    
;; Converts complex expression using the above function rco_atom only if there is a need to
;; introduce a new variable, for other cases rco_exp function handles the expression
;; READ rco_exp --- output ---> As an expression which does not contain any complex operation,
;; but it might not necessarily be an atom.
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
     (Let x (rco_exp e) (rco_exp body))]
    [_ (error "Error: Unidentified case")]))
         
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
    [(Program info e) (Program info (rco_exp e))]
    [_ (error "Error: Unidentified case")]))

;; The input to this pass will be the L_var with all the complex operation removed
;; which means operands of each operation will be atoms, (i.e Var or Int)
;; This is used to generate the tail in the grammar on page 25
(define (explicate-tail exp)
  (match exp
    [(Var x)
     (values
      (Return (Var x)) (list))]
    [(Int n)
     (values
      (Return (Int n)) (list))]
    [(Prim op es)
     (values
      (Return (Prim op es)) (list))]
    [(Let x rhs body)
     (define-values (tail-exp var-list) (explicate-tail body))
     (explicate-assign rhs x tail-exp var-list)]
    [_ (error "explicate-tail unhandled case" exp)]))

;; This function is for the creating assignment statement in C_var language (Refer the grammar on Page 25)
(define (explicate-assign exp x cont var-list)
  (match exp
    [(Var var)
     (values
      (Seq
       (Assign (Var x) (Var var)) cont)
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
     (CProgram info-dict exp-dict)]
    [_ (error "Error: Unidentified case")]))

;; Convert (Int n) --> (Imm n) so as to follow the X86 grammar
(define (int->imm exp)
  (match exp
    [(Int n) (Imm n)]
    [_ exp]))

;; select for expression (which are assignment statements, as it is the output of explicate control)
(define (select-exp exp var)
  (match exp
    [(Int int)
     (list
      (Instr 'movq (list (Imm int) var)))]
    [(Var x)
     (list
      (Instr 'movq (list (Var x) var)))]
    [(Prim 'read '())
     (list
      (Callq 'read_int 0)
      (Instr 'movq (list (Reg 'rax) var)))]
    [(Prim '- (list a))
     (list
      (Instr 'movq (list (int->imm a) var))
      (Instr 'negq (list var)))]
    [(Prim '+ (list a1 a2))
     (list
      (Instr 'movq (list (int->imm a1) var))
      (Instr 'addq (list (int->imm a2) var)))]
    [_ (error "Error: Unidentified Case")]))

;; select for statement, this function handles the special case when one of
;; the rhs of assignment is same as lhs variable.
(define (select-statement exp)
  (match exp
    [(Assign (Var var) (Prim '+ (list (Var y) a2)))
     (cond
       [(equal? var y)
        (Instr 'addq (list (int->imm a2) (Var var)))]
       [else
        (select-exp (Prim '+ (list (Var y) a2)) (Var var))])]
    [(Assign (Var var) (Prim '+ (list a1 (Var y))))
     (cond
       [(equal? var y)
        (Instr 'addq (list (int->imm a1) (Var var)))]
       [else
        (select-exp (Prim '+ (list a1 (Var y))) (Var var))])]
    [(Assign (Var var) es) (select-exp es (Var var))]
    [_ (error "Error: Unidentified Case")]))

;; select for tail (Refer the grammar of C_var for tail)
(define (select-tail exp)
  (match exp
    [(Seq stmt tail)
     (append
      (select-statement stmt)
      (select-tail tail))]
    [(Return (Prim 'read '()))
     (list
      (Callq 'read_int 0)
      (Jmp 'conclusion))]
    [(Return es)
     (append
      (select-exp es (Reg 'rax))
      (list (Jmp 'conclusion)))]
    [_ (error "Error: Unidentified Case")]))

;; Give stack-size (It must be a multiple of 16)
(define (give-st-size var-list)
  (define len (length var-list))
  (if (odd? len)
      (* (+ len 1) 8)
      (* len 8)))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
      [(CProgram info e)
       (define instr (select-tail (cdr (car e))))
       (define block (Block info instr))
       (define exp (dict-set '() 'start block))
       (define new-info (dict-set info 'stack-size (give-st-size (cdr (car info)))))
       (X86Program new-info exp)]
    [_ (error "Error: Unidentified Case")]))


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

;; Handles transformation of single instruction
(define (patch-one-instr instr)
  (match instr
    [(Instr op (list (Deref 'rbp int1) (Deref 'rbp int2)))
     (list
      (Instr 'movq (list (Deref 'rbp int1) (Reg 'rax)))
      (Instr op (list (Reg 'rax) (Deref 'rbp int2))))]
    [_ (list instr)]))

;; changes movq and addq with two stack locations as the arguments, since in X86 only 1 memory reference
;; per instruction is allowed
(define (patch-helper instr)
  (if (null? instr)
      (list)
      (append (patch-one-instr (car instr)) (patch-helper (cdr instr)))))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info exp)
     (define block (cdr (car exp)))
     (match block
       [(Block block-info instr)
        (define new-block (Block block-info (patch-helper instr)))
        (define new-exp (dict-set '() 'start new-block))
        (X86Program info new-exp)]
       [_ (error "Error: Unidentified Case")])]
    [_ (error "Error: Unidentified Case")]))


;; generates the Conclusion
(define (conclusion-gen stack-size)
  (list
  (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))
  (Instr 'popq (list (Reg 'rbp)))
  (Retq)))

;; generates Main block
(define (main-gen stack-size)
  (list 
  (Instr 'pushq (list (Reg 'rbp))) 
  (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
  (Instr 'subq (list (Imm stack-size) (Reg 'rsp)))
  (Jmp 'start)))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info exp) 
    (define stack-size (dict-ref info 'stack-size))
    (define main-block (Block '() (main-gen stack-size)))
    (define conclusion-block (Block '() (conclusion-gen stack-size)))
    (define new-exp (dict-set exp 'main main-block))
    (define final-exp (dict-set new-exp 'conclusion conclusion-block))
    (X86Program info final-exp)]
    [_ (error "Error: Unidentified Case")]))

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
    [(Callq label arity)
     (set)]  ;; for now we return an empty set, but if arity > 0, then we need to return the register used for parameter passing
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
    [(Callq label arity)
     (list->set caller-saved)]  ;; All the caller-saved registers are in the write set as mentioned on Page 36.
    [(Retq) (set)]
    [_ (set)]))
  

;; Takes a X86 instruction and live-before set and gives the live after set
(define (live-before-op instr live-before)
  (set-union (set-subtract live-before (write-set instr)) (read-set instr)))
  
;; Takes a list of instructions and compute the live after sets, (list of sets)
(define (live-before instrs live-before-set)
  (match instrs
    [(list) (list)]
    [_
     (define new-set (live-before-op (car instrs) live-before-set))
     (cons new-set (live-before (cdr instrs) new-set))]))
     
;; Uncover-live pass
(define (uncover-live-pass p)
  (match p
    [(X86Program info exp)
     (define block (dict-ref exp 'start))
     (match block
       [(Block b-info instrs)
        (define live-before-list (live-before (reverse instrs) (set)))
        (define new-info (dict-set b-info 'live-before (reverse live-before-list)))
        (define new-block (Block new-info instrs))
        (X86Program info (dict-set info 'start new-block))]
       [_ (error "Error: Unidentified Case while matching Block of X86Program in uncover-live-pass")])]
    [_ (error "Error: Unidentified Case while matching X86Program in uncover-live-pass")]))

;; Process single instruction, returns list of edges, where an edge is a list of two elements, source and vertex
(define (generate-edges instr live-after-set)
  (match instr
    [(Instr 'movq (list a b))
     (map (lambda (x) (if (or (equal? x a) (equal? x b)) (list) (list b x))) (set->list live-after-set))]
    [_
     (define write-sett (write-set instr))
     (map (lambda (x) (if (equal? (car x) (cadr x)) (list) x)) (cartesian-product (set->list write-sett) (set->list live-after-set)))]
    ))

    
;; Process list of instructions
(define (build-graph-exp instrs live-after)
  (match instrs
    [(list a) (list)]
    [_
     (append
      (generate-edges (car instrs) (car live-after))
      (build-graph-exp (cdr instrs) (cdr live-after)))]))

;; Remove empty edges
(define (remove-empty-edge edges)
  (if (null? edges)
      (list)
      (match (car edges)
        [(list a b) (cons (car edges) (remove-empty-edge (cdr edges)))]
        [_ (remove-empty-edge (cdr edges))])))

;; Remove redundant edges
(define (remove-redundant-edges edges) (set->list (list->set edges)))

;; Build interference graph
(define (build-graph p)
  (match p
    [(X86Program info exp)
     (define block (dict-ref exp 'start))
     (match block
       [(Block b-info instrs)
        (define live-bef (dict-ref b-info 'live-before))
        (define edges (build-graph-exp instrs (cdr live-bef)))
        (define correct-edges  (remove-redundant-edges (remove-empty-edge edges)))
        ;;(print correct-edges)
        (printf (graphviz (undirected-graph correct-edges)))
        (X86Program (dict-set info 'conflict (undirected-graph correct-edges)) exp)]
       [_ (error "Error: Unidentified Case while matching Block of X86Program in build-graph pass")])]
    [_ (error "Error: Unidentified Case while matching X86Program in build-graph pass")]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ;;("partial-evaluator" ,partial-lvar ,interp-Lvar)
     ;;("optimized-par-eval" ,opt-par-lvar ,interp-Lvar)
     ("shrink" ,shrink ,interp-Lif)
     ("uniquify" ,uniquify ,interp-Lif)
     ;;("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ;;("explicate control" ,explicate-control ,interp-Cvar)
     ;;("instruction selection" ,select-instructions ,interp-x86-0)
     ;;("uncover live" ,uncover-live-pass ,interp-x86-0)
     ;;("build graph" ,build-graph ,interp-x86-0)
     ;;("assign homes" ,assign-homes ,interp-x86-0)
     ;;("patch instructions" ,patch-instructions ,interp-x86-0)
     ;;("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

