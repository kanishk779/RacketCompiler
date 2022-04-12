; (let ([x 10])
;     (let ([sum 0])
;         (let ([y (while (> x 0) 
;             (begin 
;                 (set! sum (+ sum x))
;                 (set! x (- x 2))
;                 ;; create while, let, if
;                 (let ([z 8]) (+ z 10))
;                 (if (> x 1) 10 20)
;                 (while (> x 1)
;                     (begin
;                         (+ 10 20)
;                         (set! sum (+ sum x))
;                         (set! x (- x 2))
;                     )
;                 )
;                 (+ 30 40)
;             ))])
;             sum
;         )
;     )
; )

(let ([v (vector (- 20) (+ 22 20))])
  (+ (vector-ref v 0) (vector-ref v 1)))
