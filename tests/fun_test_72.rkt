(define (my-f [v : (Vector Integer Integer Integer)] [index : Integer] [times : Integer]) : Integer
  	(begin
		(while (> times 0)
			(begin
				(set! times (- times 1))
				(vector-set! v 0 (+ (vector-ref v 0) 1))
			)
		)
		(+ (vector-length v) (vector-ref v 0))
	)
)

(let ([x (my-f (vector 3 4 5) 1 5)])
	(if (> x 10)
		(+ 10 (my-f (vector 1 2 3) 1 3))
		(- 100 (my-f (vector 1 2 3) 0 10))
	)
)
