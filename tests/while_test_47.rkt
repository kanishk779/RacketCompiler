(begin
    (read)
    (let ([x (read)]) 
        (begin
            (while (> x 5)
                (begin
                    (set! x (- x 2))
                )
            )
            x
        )
    )
)