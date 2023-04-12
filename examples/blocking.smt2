(declare-const r1 Relation)
(assert (global true)) ; Should be killed by simplifier
(assert (global (dia r1 (dia r1 (dia r1 true)))))
