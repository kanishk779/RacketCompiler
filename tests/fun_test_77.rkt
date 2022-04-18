(define (useless [x: Integer]): Integer
    (let ([sum 0])
        (begin
            (while (> x 0)
                (begin
                    (set! x (- x 1))
                    (set! sum (+ sum 2))
                )
            )
            sum
        )
    )
)
(begin
    (let ([x (useless 10)])
        x
    )
    (if (< (useless 5) 20)
        (useless 2)
        (useless 3)
    )
    (while #f
        (useless (read))
    )
    (useless 7)
    42
)