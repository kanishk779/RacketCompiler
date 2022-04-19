(+ 10 35)
; (let ([v (vector 1 2 3)]) 
;     (let ([iter (vector-length v)]) 
;         (begin
;             (while (> iter 0) 
;                 (begin
;                     (set! iter (- iter 1))
;                     (let ([curr (vector-ref v iter)])
;                         (begin
;                             (vector-set! v (- curr 1) (- curr))
;                             10
;                         ) 
;                     )
;                 )
;             )
;             (let ([i (vector-length v)]) 
;                 (let ([sum 0]) 
;                     (begin
;                         (while (> i 0) 
;                             (begin 
;                                 (set! i (- i 1))
;                                 (set! sum (+ sum (vector-ref v i)))
;                             )
;                         )
;                         (- sum)
;                     )
;                 )
;             )
;         )
;     )
; )