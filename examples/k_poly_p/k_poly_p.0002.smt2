(declare-const r Relation)
(declare-fun p1 (World) Bool)
(declare-fun p2 (World) Bool)
(declare-fun p3 (World) Bool)
(declare-fun p4 (World) Bool)
(declare-fun p5 (World) Bool)
(declare-fun p6 (World) Bool)
(declare-fun p7 (World) Bool)
(declare-fun p8 (World) Bool)
(declare-fun p9 (World) Bool)
(declare-fun p10 (World) Bool)
(declare-fun p12 (World) Bool)
(declare-fun p14 (World) Bool)
(declare-fun p16 (World) Bool)
(assert (not (or (or (box r (box r (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (p1 world) (p2 world)) (p3 world)) (p4 world)) (p5 world)) (p6 world)) (p7 world)) (p8 world)))))))))) (or (dia r (or (or (dia r (or (or (dia r (or (or (dia r (or (or (dia r (or (or (dia r (or (or (dia r (or false (dia r (= (p1 world) (p2 world))))) (box r (p3 world))) (dia r (dia r (= (p2 world) (p3 world)))))) (box r (p4 world))) (dia r (dia r (dia r (= (p3 world) (p4 world))))))) (box r (p5 world))) (dia r (dia r (dia r (dia r (= (p4 world) (p5 world)))))))) (box r (p6 world))) (dia r (dia r (dia r (dia r (dia r (= (p5 world) (p6 world))))))))) (box r (p7 world))) (dia r (dia r (dia r (dia r (dia r (dia r (= (p6 world) (p7 world)))))))))) (box r (p8 world))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (= (p7 world) (p1 world))))))))))) (box r (p9 world)))) (box r (box r (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (not (p2 world)) (not (p4 world))) (not (p6 world))) (not (p8 world))) (not (p10 world))) (not (p12 world))) (not (p14 world))) (not (p16 world))))))))))))))
