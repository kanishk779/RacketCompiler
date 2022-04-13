(let ([v (vector 1 2 3 4 5 6 7)]) 
    (let ([p 0]) 
        (let ([loop (while (< p 7) 
            (begin 
                (set! p (+ p 1))
                (vector-ref v p)))]) (10))))