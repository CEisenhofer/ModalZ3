; sat
(declare-const r1 Relation)

(assert (box r1 (dia r1 true)))
(assert (dia r1 true))

(assert (trans r1))
