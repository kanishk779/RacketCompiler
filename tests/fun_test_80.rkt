(define (my-find [x: Integer] [v: (Vector Integer Integer Integer Integer)]): Boolean
    (let ([index 0])
        (let ([found #f])
            (begin
                (while (< index (vector-length v))
                    (begin
                        (if (eq? x (vector-ref v index))
                            (set! found #t)
                            (void)
                        )
                        (set! index (+ index 1))
                    )
                )
                found
            )
        )
    )
)

(define (find-MEX [v: (Vector Integer Integer Integer Integer)])
    (let ([ans -1])
        (let ([num 0])
            (let ([len (vector-length v)])
                (begin
                    (while (<= num len)
                        (begin
                            (let ([found (my-find num v)])
                                (if (and (not found) (eq? ans -1))
                                    (set! ans num)
                                    (set! ans ans)
                                )
                            )
                            (set! num (+ num 1))
                        )
                    )
                    ans
                )
            )
        )
    )
)


(+ 
    (find-MEX (vector 0 1 2 3))
    (+ 35 (find-MEX (vector 0 2 8 1)))
)