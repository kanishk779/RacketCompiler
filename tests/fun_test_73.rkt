(define (tail-sum [n: Integer] [r: Integer]): Integer
  (if (eq? n 0)
	r
	(tail-sum (- n 1) (+ n r))
	)
  )
(define (noob-sum [n: Integer]): Integer
  (if (eq? n 0)
	0
	(+ n (noob-sum (- n 1)))))

(let ([x (tail-sum 5 0)])
  (let ([y (noob-sum 5)])
	(if (eq? x y)
	  42
	  52)))
