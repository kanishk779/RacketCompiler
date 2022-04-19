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

; (vector-ref (vector-ref (vector (vector 42)) 0) 0)
; (+
    ; (let ([sum (vector-ref (vector 2 3 4 ) 0)])
    ;     (begin
    ;         (while (< sum 10)
    ;             (begin
    ;                 (set! sum (+ sum 3))
    ;             )
    ;         )
    ;         (- sum 3)
    ;     )
    ; )
    ; (if (< 10 20)
        (let ([i 5])
            (let ([v1 (vector 2)])
            (begin
                (while (> i 0)
                    (begin 
                        (if (> i 2) 
                            (vector-set! v1 0 (+ (vector-ref v1 0) i)) 
                            (vector-set! v1 0 (vector-ref v1 0))
                        )
                        (set! i (- i 1))
                    )
                )
                (vector-ref v1 0)
            ))
        )
    ;     (+ (read) 10)
    ; )
; )
