(let ([v (vector 1 2 3 4 5 6 7 8 9 10)]) 
    (let ([u (vector 10 20 30 40 50 60 70)]) 
        (let ([q (vector 15 16 17 18 19 #t #f (vector 1 2 3))]) 
            (vector-ref q 3))))