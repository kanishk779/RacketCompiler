(+ 
    (let ([sum 0]) (let ([i 10]) 
        (begin
            (while (> i 0) 
            (begin (set! sum (+ sum i)) (set! i (- i 2)))
            )
            sum
        )
    ))
    (- 10 5)
)