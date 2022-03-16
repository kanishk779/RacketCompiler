(if 
    (let 
        ([x 
            (and 
                (if #t (< (+ 10 (- (read))) 20) #f) 
                (not (and #f #t)) 
            )
        ]) 
        (or (not x) #f))
    10
    20
)