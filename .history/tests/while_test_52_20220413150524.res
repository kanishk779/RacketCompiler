(let ([x 
    (+ (let ([y 10]) (+ y 4)) (let ([z (read)]) (let ([loop (while (< z 6) (begin 
        (set! z (+ z 3))
        (set! x (+ x 4))
        (+ 7 9)
        (if (> x 100) (- x 60) (100))))]) (+ x z))))]) 
    (let ([total 0]) 
        (let ([count 0])
            (let ([loop (while (< count 20) 
                (begin 
                    (set! count (+ count 3)) 
                    (set! total (+ total count)) 
                    (if (= count 9) 10 20)
                    (let ([second (while (< total 20) 
                        (begin 
                            (set! total (+ total 20))
                            (+ 9 7)))]) (+ 4 8))))]) 
                    (+ count total)))))