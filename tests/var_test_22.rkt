(if 
    (and #f (or #t #f))
    (if 
        #f 
        10 
        (+ (+ 30 (let ([x 22]) (+ x 10))) 20)
    )
    (let 
        ([x (if (< 10 30) 20 30)]) 
        (if (eq? x 20) x (+ x 10))
    )
)
