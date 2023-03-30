(declare-const r1 Relation)
(declare-fun p (World) Bool)
(assert (box r1 (not (p world))))
(assert (dia r1 (p world)))
