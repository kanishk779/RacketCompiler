(begin
    (begin
        (read)
        (let ([x (read)])
            (+ x 10)
        )
        (if (eq? 10 10)
            (let ([x 10])
                (while (> x 3)
                    (begin
                        (set! x (- x 2))
                        (+ 7 9)
                    )
                )
            )
            (begin
                (+ 10 20)
                (void)
            )
        )
    )
    10
)