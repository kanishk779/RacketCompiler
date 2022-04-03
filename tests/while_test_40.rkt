(let ([x 2])
    (+ (begin (set! x 40) x) x)
)