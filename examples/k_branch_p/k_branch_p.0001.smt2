(declare-const r Relation)
(declare-fun p100 (World) Bool)
(declare-fun p101 (World) Bool)
(declare-fun p102 (World) Bool)
(declare-fun p0 (World) Bool)
(declare-fun p1 (World) Bool)
(assert (not (or (not (and (and (p100 world) (not (p101 world))) (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world))))))))) (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world))))))) (box r (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world))))))))) (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world))))))))))) (not (box r (p1 world))))))