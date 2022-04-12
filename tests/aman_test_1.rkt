;;(let ([y (let ([x 20]) (+ x (let ([x 22]) x)))]) y)
; (+ (- 10) (- 56))
; (let ([x 20]) (let ([x (+ 1 x)]) x))

(let ([sum 0])
    (let ([i 5])
        (begin
            (while (> i 0)
                (begin 
                    (set! sum (+ sum i))
                    (set! i (- i 1))
                )
            )
            sum
        )
    )
)
