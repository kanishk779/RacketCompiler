(if (and
        (let 
            ([x 
                (if 
                    (eq? 30 (+ 12 18)) 
                    (< 10 30) 
                    (>= 30 40)
                )
            ]) 
            (or x #f) 
        )
        (if 
            (<= 20 40) 
            (not (and #t #f)) 
            (not (or #t #f))
        )
    )
    10
    20
)