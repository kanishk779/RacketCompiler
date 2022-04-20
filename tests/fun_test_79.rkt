(define (inc-2 [x : Integer]) : Integer
    (+ x 2)
)

(define (inc-3 [x : Integer]) : Integer
    (+ x 3)
)

(define (my-f [x : Integer] [arg : Integer] [v : (Vector (Integer -> Integer) (Integer -> Integer))]) : Integer
    (if (< x 10)
        ((vector-ref v 0) arg)
        ((vector-ref v 1) arg)
    )
)

(+ 
    (my-f 6 30 (vector inc-2 inc-3))
    (my-f 11 7 (vector inc-2 inc-3))
)