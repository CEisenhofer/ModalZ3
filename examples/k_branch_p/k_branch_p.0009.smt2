(declare-const r Relation)
(declare-fun p100 (World) Bool)
(declare-fun p101 (World) Bool)
(declare-fun p102 (World) Bool)
(declare-fun p103 (World) Bool)
(declare-fun p104 (World) Bool)
(declare-fun p105 (World) Bool)
(declare-fun p106 (World) Bool)
(declare-fun p107 (World) Bool)
(declare-fun p108 (World) Bool)
(declare-fun p109 (World) Bool)
(declare-fun p110 (World) Bool)
(declare-fun p0 (World) Bool)
(declare-fun p1 (World) Bool)
(declare-fun p2 (World) Bool)
(declare-fun p3 (World) Bool)
(declare-fun p4 (World) Bool)
(declare-fun p5 (World) Bool)
(declare-fun p6 (World) Bool)
(declare-fun p7 (World) Bool)
(declare-fun p8 (World) Bool)
(declare-fun p9 (World) Bool)
(assert (not (or (not (and (and (p100 world) (not (p101 world))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))) (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))))) (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world))))))))))) (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))))))) (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world))))))))))))) (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))))))))) (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world))))))))))))))) (box r (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))))))))))) (box r (box r (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world))))))))))))))))) (box r (box r (box r (box r (box r (box r (box r (box r (box r (and (and (and (and (and (and (and (and (and (and (and (=> (p101 world) (p100 world)) (=> (p102 world) (p101 world))) (=> (p103 world) (p102 world))) (=> (p104 world) (p103 world))) (=> (p105 world) (p104 world))) (=> (p106 world) (p105 world))) (=> (p107 world) (p106 world))) (=> (p108 world) (p107 world))) (=> (p109 world) (p108 world))) (=> (p110 world) (p109 world))) (and (and (and (and (and (and (and (and (and (=> (p100 world) (and (=> (p0 world) (box r (=> (p100 world) (p0 world)))) (=> (not (p0 world)) (box r (=> (p100 world) (not (p0 world))))))) (=> (p101 world) (and (=> (p1 world) (box r (=> (p101 world) (p1 world)))) (=> (not (p1 world)) (box r (=> (p101 world) (not (p1 world)))))))) (=> (p102 world) (and (=> (p2 world) (box r (=> (p102 world) (p2 world)))) (=> (not (p2 world)) (box r (=> (p102 world) (not (p2 world)))))))) (=> (p103 world) (and (=> (p3 world) (box r (=> (p103 world) (p3 world)))) (=> (not (p3 world)) (box r (=> (p103 world) (not (p3 world)))))))) (=> (p104 world) (and (=> (p4 world) (box r (=> (p104 world) (p4 world)))) (=> (not (p4 world)) (box r (=> (p104 world) (not (p4 world)))))))) (=> (p105 world) (and (=> (p5 world) (box r (=> (p105 world) (p5 world)))) (=> (not (p5 world)) (box r (=> (p105 world) (not (p5 world)))))))) (=> (p106 world) (and (=> (p6 world) (box r (=> (p106 world) (p6 world)))) (=> (not (p6 world)) (box r (=> (p106 world) (not (p6 world)))))))) (=> (p107 world) (and (=> (p7 world) (box r (=> (p107 world) (p7 world)))) (=> (not (p7 world)) (box r (=> (p107 world) (not (p7 world)))))))) (=> (p108 world) (and (=> (p8 world) (box r (=> (p108 world) (p8 world)))) (=> (not (p8 world)) (box r (=> (p108 world) (not (p8 world)))))))) (=> (p109 world) (and (=> (p9 world) (box r (=> (p109 world) (p9 world)))) (=> (not (p9 world)) (box r (=> (p109 world) (not (p9 world))))))))) (and (and (and (and (and (and (and (and (=> (and (p100 world) (not (p101 world))) (and (dia r (and (and (p101 world) (not (p102 world))) (p1 world))) (dia r (and (and (p101 world) (not (p102 world))) (not (p1 world)))))) (=> (and (p101 world) (not (p102 world))) (and (dia r (and (and (p102 world) (not (p103 world))) (p2 world))) (dia r (and (and (p102 world) (not (p103 world))) (not (p2 world))))))) (=> (and (p102 world) (not (p103 world))) (and (dia r (and (and (p103 world) (not (p104 world))) (p3 world))) (dia r (and (and (p103 world) (not (p104 world))) (not (p3 world))))))) (=> (and (p103 world) (not (p104 world))) (and (dia r (and (and (p104 world) (not (p105 world))) (p4 world))) (dia r (and (and (p104 world) (not (p105 world))) (not (p4 world))))))) (=> (and (p104 world) (not (p105 world))) (and (dia r (and (and (p105 world) (not (p106 world))) (p5 world))) (dia r (and (and (p105 world) (not (p106 world))) (not (p5 world))))))) (=> (and (p105 world) (not (p106 world))) (and (dia r (and (and (p106 world) (not (p107 world))) (p6 world))) (dia r (and (and (p106 world) (not (p107 world))) (not (p6 world))))))) (=> (and (p106 world) (not (p107 world))) (and (dia r (and (and (p107 world) (not (p108 world))) (p7 world))) (dia r (and (and (p107 world) (not (p108 world))) (not (p7 world))))))) (=> (and (p107 world) (not (p108 world))) (and (dia r (and (and (p108 world) (not (p109 world))) (p8 world))) (dia r (and (and (p108 world) (not (p109 world))) (not (p8 world))))))) (=> (and (p108 world) (not (p109 world))) (and (dia r (and (and (p109 world) (not (p110 world))) (p9 world))) (dia r (and (and (p109 world) (not (p110 world))) (not (p9 world)))))))))))))))))))) (not (box r (box r (box r (box r (box r (box r (box r (box r (box r (p4 world))))))))))))))
