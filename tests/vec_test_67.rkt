(+ 
(vector-ref (vector 1 2 3 4 #t (vector 1 2 3 4) (vector-length (vector 1 #t))) 3) 
(vector-length (vector 1 2 3 4 (vector-length (vector 1 2)))))