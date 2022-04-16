(let ([v (vector 1 2 3 4 5 6 7 8 9)]) 
    (let ([iter (vector-length v)]) 
        (while (> iter 0) 
            (begin
                (set! iter (- iter 1))
                (let ([curr (vector-ref v iter)]) 
                    (vector-set! v (- curr 1) (- curr))))) 
                    
                    (let ([i (vector-length v)]) 
                        (let ([sum 0]) 
                            (while (> i 0) (begin 
                                (set! i (- i 1))
                                (set! sum (+ sum (vector-ref v i)))
                                ))
                                (- sum)))))