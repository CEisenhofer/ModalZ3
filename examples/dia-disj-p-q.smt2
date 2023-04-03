(declare-const r1 Relation)
(declare-fun p (World) Bool)
(declare-fun q (World) Bool)

(assert (dia r1 (or (p world) (q world))))
