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

(vector-ref (vector-ref (vector (vector 42)) 0) 0)
; (vector-ref (vector 42 (read) (let ([x 1]) x) (if #t 5 6)) 0)
