(let 
  ([x (+ 5 (- 20))])
  (+ (let ([x (+ (read) (- (read)))]) x) x))
