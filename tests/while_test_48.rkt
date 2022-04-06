(begin
    (begin
        (read)
        (let ([x (read)])
            (+ x 10)
        )
        (let ([y 5])
            (if (> y 2)
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
    )
    10
)