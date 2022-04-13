(let ([t1 (vector (if #t 4 3) 6)])
	(let ([t2 t1])
		(let ([_ (vector-set! t2 1 2)])
			(vector-ref t1 0))))