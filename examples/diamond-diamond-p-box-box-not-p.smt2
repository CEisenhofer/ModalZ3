(declare-const r1 Relation)
(declare-const r2 Relation)
(declare-fun p (World) Bool)
(declare-fun q (World) Bool)

(assert (dia r1 (dia r2 (p world))))
(assert (box r1 (box r2 (and 
    (not (p world)) 
    (q world); just here to confuse the preprocessor
))))
