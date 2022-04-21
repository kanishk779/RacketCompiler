(let ([v (vector 1 2 3)])
    (begin
        (vector-ref v 0)
        (while (< 10 5) 
            (begin
                (vector-ref v 0)
                (vector-ref v 1)
            )
        )
        (+ 33 (vector-ref v 2))
    )
)
; (let ([v (vector (read) 2 3 4)])
;     (let ([q (read)]) 
;         (let ([total 0])
;             (begin
;                 (while (> q 0) 
;                     (begin
;                         (set! q (- q 1))
;                         (set! total (+ total (vector-ref v 0)))
;                         (vector-set! v 0 (read))
;                     )
;                 )
;                 total
;             )     
;         )
;     )
; )