(declare-const r Relation)
(declare-fun p1 (World) Bool)
(declare-fun p2 (World) Bool)
(declare-fun p3 (World) Bool)
(declare-fun p4 (World) Bool)
(declare-fun p5 (World) Bool)
(declare-fun p6 (World) Bool)
(declare-fun p8 (World) Bool)
(assert (not (or (or (box r (box r (box r (box r (and (and (and (p1 world) (p2 world)) (p3 world)) (p4 world)))))) (or (dia r (or (or (dia r (or (or (dia r (or false (dia r (= (p1 world) (p2 world))))) (box r (p3 world))) (dia r (dia r (= (p2 world) (p3 world)))))) (box r (p4 world))) (dia r (dia r (dia r (= (p3 world) (p1 world))))))) (box r (p5 world)))) (box r (box r (box r (box r (and (and (and (not (p2 world)) (not (p4 world))) (not (p6 world))) (not (p8 world))))))))))
