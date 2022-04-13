(let ([v (vector 1 2 3 4 5 6 7)]) 
    (let ([p 0]) 
        (let ([loop (while (< p 7) 
            (begin 
                (vector-ref v p)
                (set! p (+ p 1))
                ))]) (10))))