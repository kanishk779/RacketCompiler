(let ([x 20]) 
    (begin
        10
        (read)
        (let ([y (set! x 22)]) y)
        (- 30 x)
    )
)