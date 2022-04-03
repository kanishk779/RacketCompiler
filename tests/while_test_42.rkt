(let ([x 3])
    (let ([y 5])
        (+ 
            (+
                (begin (set! y (read)) x)
                (begin (set! x (read)) y)
            ) 
            x
        )
    )
)