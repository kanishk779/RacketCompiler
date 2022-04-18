(define (male [n: Integer]): Integer
  (if (< n 0)
	0
	(if (eq? n 0)
	  1
	  (- n (female (male (- n 1)))))))

(define (female [n: Integer]): Integer
  (if (< n 0)
	0
	(if (eq? n 0)
	  0
	  (- n (male (female (- n 1)))))))


(+ (male 3) (female 3))
