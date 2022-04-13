(let ([x 
    (+ (let ([y 10]) (+ y 4)) (let ([z (read)]) (- z)))]) 
    (let ([total 0]) 
        (let ([count 0])
            (let ([loop (while (< count 20) 
                (begin 
                    (set! count (+ count 3)) 
                    (set! total (+ total count)) 
                    (if (= count 9) 10 20)))]) 
                    (+ count total)))))