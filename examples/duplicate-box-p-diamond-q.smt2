(declare-const r1 Relation)
(declare-fun p (World) Bool)
(declare-fun q (World) Bool)

(assert 
    (or 
        (and (box r1 (p world)) (dia r1 (q world))) 
        (and (box r1 (not (p world))) (dia r1 (q world)))
    )
)
