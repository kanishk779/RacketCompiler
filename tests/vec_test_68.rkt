(+ 
    (let ([x (vector-length (vector 1 2 3 (vector #t #f #t #f 1 2) (vector-length (vector 1 2 3 4 5))))])
        (let ([counter 5]) 
            (let ([sum 0]) 
                (begin
                    (while (> counter 0) 
                        (begin
                            (set! counter (- counter 1))
                            (set! sum (+ sum 10))
                            (if (> sum 20) 
                                (set! sum (+ sum 5)) 
                                (set! sum (- sum 20))
                            )
                        )
                    ) 
                    (+ sum 4)
                )
            )
        )
    )
    56
)

; (+  (let ([iter (vector-length (vector 1 2 3 4 5 6 7 8 9))]) 
;             (let ([sum 0]) 
;                 (begin
;                     (while (> iter 0)
;                         (begin 
;                             (set! iter (- iter 1))
;                             (set! sum (+ sum (vector-ref (vector 1 2 3 4 5 6 7 8 9) iter)))
;                             (if (> iter 5) (set! sum (- sum)) (set! sum (+ sum 1)))
;                         )
;                     )
;                     sum
;                 )
;             )
;         )
;         (+ 37 
;             (let ([v (vector 1 2 3 4 5 6 7 8 9)]) 
;                 (let ([iter (vector-length v)]) 
;                     (let ([total 0]) 
;                         (begin
;                             (while (> iter 0) 
;                                 (begin 
;                                     (set! iter (- iter 1))
;                                     (set! total (+ total total))
;                                     (vector-set! v iter (vector total))
;                                 )
;                             ) 
;                             (vector-ref (vector-ref v 0) 0)
;                         )
;                     )
;                 )
;             )
;         )
;     )