(declare-const r Relation)
(declare-fun p101 (World) Bool)
(declare-fun p102 (World) Bool)
(declare-fun p201 (World) Bool)
(declare-fun p202 (World) Bool)
(declare-fun p301 (World) Bool)
(declare-fun p302 (World) Bool)
(assert (not (=> (dia r (and (and (or (p101 world) (box r (p102 world))) (or (p201 world) (p202 world))) (or (p301 world) (p302 world)))) (dia r (or (or (or (or (or (and (p101 world) (p201 world)) (and (p101 world) (p301 world))) (and (p201 world) (p301 world))) (and (box r (p102 world)) (p202 world))) (and (box r (p102 world)) (p302 world))) (and (p202 world) (p302 world)))))))
