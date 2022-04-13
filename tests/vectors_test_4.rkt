(let ([v (vector 1 2 3 4 5 6 7)])
    (+ (vector-ref v (vector-ref v 2)) 
        (vector-ref v (vector-ref v 0))))