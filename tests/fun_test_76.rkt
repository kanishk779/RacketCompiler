(define (useless1 [x: Integer] [y: Integer]): Boolean
    (< (+ x 10) (- y 10))
)

(define (useless2 [x: Integer] [y: Integer]): Boolean
    (> (- x 2) (+ y 1))
)
(define (my-f [x: Integer] [y: Integer]): (Integer Integer) -> Integer
    (if (< x y)
        useless1
        useless2
    )
)
(let ([x (read)])
    (let ([y (read)])
        (let ([new-f (my-f x y)])
            (if (new-f x y)
                42
                52
            )
        )
    )
)