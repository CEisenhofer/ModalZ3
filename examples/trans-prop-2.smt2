; sat
(declare-fun p (World) Bool)
(declare-const r1 Relation)
(declare-const r2 Relation)

(assert (dia r1 (dia r1 (dia r2 (p world)))))
(assert (box r1 (not (p world))))
(assert (trans r1))
