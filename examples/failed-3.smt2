(declare-const r1 Relation)
(declare-fun p (World) Bool)

(assert (dia r1 true))
(assert (box r1 (dia r1 (p world))))
