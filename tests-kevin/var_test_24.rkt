(if (or
        (if 
            (let ([x (eq? 40 (- 80 40))]) (not x)) 
            (or #t (>= 30 20)) 
            #f
        )
        (and 
            (let ([y #t]) (and #t y)) 
            (not #t)
        )
    )
    10
    20
)
