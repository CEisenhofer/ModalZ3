(declare-const r1 Relation)
(declare-fun p (World) Bool)
(assert (dia r1 (p world)))
(assert (dia r1 (not (p world))))
