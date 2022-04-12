(vector-ref
 (vector-ref
(let ([vecinit7976
(let ([vecinit7972 42])
(let ([collectret7974
(if (< (+ (global-value free_ptr) 16)
(global-value fromspace_end)) (void)
(collect 16)
)])
(let ([alloc7971 (allocate 1 (Vector Integer))])
(let ([initret7973 (vector-set! alloc7971 0 vecinit7972)]) alloc7971))))])
(let ([collectret7978
(if (< (+ (global-value free_ptr) 16)
(global-value fromspace_end)) (void)
(collect 16)
)])
(let ([alloc7975 (allocate 1 (Vector (Vector Integer)))])
(let ([initret7977 (vector-set! alloc7975 0 vecinit7976)]) alloc7975))))
0) 0)