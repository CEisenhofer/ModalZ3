(declare-const r Relation)
(declare-fun p1 (World) Bool)
(declare-fun p2 (World) Bool)
(declare-fun p3 (World) Bool)
(declare-fun p5 (World) Bool)
(declare-fun p4 (World) Bool)
(declare-fun p6 (World) Bool)
(assert (not (or (or (or (or (or (box r (p1 world)) (box r (p2 world))) (box r (p3 world))) (box r (p5 world))) (or (or (or (or (or (or false false) (or false false)) (or false false)) (or false false)) (or false false)) (or false false))) (or (or (or (dia r (not (p2 world))) (dia r (not (p4 world)))) (dia r (not (p2 world)))) (dia r (not (p6 world)))))))