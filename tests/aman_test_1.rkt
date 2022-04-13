;;(let ([y (let ([x 20]) (+ x (let ([x 22]) x)))]) y)
; (+ (- 10) (- 56))
; (let ([x 20]) (let ([x (+ 1 x)]) x))

; (let ([sum 0])
;     (let ([i 5])
;         (begin
;             (while (> i 0)
;                 (begin 
;                     (set! sum (+ sum i))
;                     (set! i (- i 1))
;                 )
;             )
;             sum
;         )
;     )
; )

; (vector-ref (vector-ref (vector (vector 43)) 0) 0)
(vector-ref
(vector-ref
(let ([vecinit6
(let ([_4 (if (< (+ (global-value free_ptr) 16)
(global-value fromspace_end))
(void)
(collect 16))])
(let ([alloc2 (allocate 1 (Vector Integer))])
(let ([_3 (vector-set! alloc2 0 42)])
alloc2)))])
(let ([_8 (if (< (+ (global-value free_ptr) 16)
(global-value fromspace_end))
(void)
(collect 16))])
(let ([alloc5 (allocate 1 (Vector (Vector Integer)))])
(let ([_7 (vector-set! alloc5 0 vecinit6)])
alloc5))))
0)
0)
