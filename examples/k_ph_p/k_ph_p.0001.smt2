(declare-const r Relation)
(declare-fun p101 (World) Bool)
(declare-fun p201 (World) Bool)
(assert (not (=> (dia r (and (p101 world) (p201 world))) (dia r (and (p101 world) (p201 world))))))
