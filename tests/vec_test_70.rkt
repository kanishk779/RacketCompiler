37
; (let ([v (vector (read) (read) (read) (read) (read) (read) (read) (read) (read))])
;     (let ([q (read)]) 
;         (let ([total 0])
;             (begin
;                 (while (> q 0) 
;                     (begin
;                         (set! q (- q 1))
;                         (set! total (+ total (vector-ref v (read))))
;                         (vector-set! v (read) (read))
;                     )
;                 )
;                 total
;             )     
;         )
;     )
; )