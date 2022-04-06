(let ([x 20]) 
    (begin
        10
        (let ([y (set! x 22)]) y)
        (- 30 x)
    )
)