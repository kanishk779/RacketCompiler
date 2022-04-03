(if (< 10 20)
    (let ([i 5])
        (let ([sum 0])
        (begin
            (while (> i 0)
                (begin (if (> i 2) (set! sum (+ sum i)) (set! sum sum)) (set! i (- i 1)) )
            )
            sum
        ))
    )
    (+ (read) 10)
)