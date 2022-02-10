(let
  ([x (+ (- (read)) 
    (let
        ([y (+ (- 10) (read))])
        (- (+ y (let
                  ([x (+ -98 -32)])
                  x)))))])
  (+ x (read)))
