(let ([v (vector 1 2 3 4 5 6 7)]) 
    (let ([p 0])  
        (let ([total 0])  
            (begin 
            (while (< p 7) 
                (begin 
                    (set! total (+ total (vector-ref v 0)))
                    (set! p (+ p 1))
                    )) (+ (read) total)))))