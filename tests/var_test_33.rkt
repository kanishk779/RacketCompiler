(if
    (let ([x (- (read))]) (eq? x 20))
    (if
        (let ([x #t]) (not (and x (or #f x))))
        (- (+ 20 30))
        (let 
            ([x (if #t (+ 10 20) 10)]) 
            (- x 5)
        )
    )
    (let ([y 10]) (- y 5))
)