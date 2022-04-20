(define (actually-useless [x : Integer]) : Integer
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

(define (my-find [x : Integer] [v : (Vector Integer Integer Integer Integer)]) : Boolean
    (let ([index 0])
        (let ([found #f])
            (begin
                (while (< index (vector-length v))
                    (begin
                        (if (eq? x (vector-ref v 0))
                            (set! found #t)
                            (void)
                        )
                        (set! index (+ index 1))
                    )
                )
                found
            )
        )
    )
)

(if (or (my-find 3 (vector 1 2 3 4)) (my-find 10 (vector 1 2 3 4)))
    42
    52
)