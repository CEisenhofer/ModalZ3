(declare-const r Relation)
(declare-fun p1 (World) Bool)
(declare-fun p2 (World) Bool)
(declare-fun p3 (World) Bool)
(declare-fun p5 (World) Bool)
(declare-fun p6 (World) Bool)
(declare-fun p4 (World) Bool)
(assert (not (or (or (or (or (or (box r (p1 world)) (box r (p2 world))) (box r (p3 world))) (box r (p5 world))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (dia r (and (not (p1 world)) (box r (p3 world)))) (dia r (and (not (p1 world)) (box r (p5 world))))) false) (or (dia r (and (not (p2 world)) (box r (p1 world)))) false)) (or (or (dia r (and (not (p3 world)) (box r (p3 world)))) (dia r (and (not (p3 world)) (box r (p5 world))))) false)) (or false false)) (or (or (dia r (and (not (p5 world)) (box r (p3 world)))) (dia r (and (not (p5 world)) (box r (p5 world))))) false)) (or false false)) (or (or (or (or (dia r (dia r (and (not (p1 world)) (box r (p1 world))))) (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))) (dia r (dia r (and (not (p1 world)) (box r (p6 world)))))) (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))) false)) (or false (or (dia r (and (not (p4 world)) (box r (p2 world)))) (dia r (and (not (p6 world)) (box r (p2 world))))))) (or (or (or (dia r (dia r (and (not (p3 world)) (box r (p1 world))))) (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))) (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))) false)) (or false (or (dia r (and (not (p4 world)) (box r (p4 world)))) (dia r (and (not (p6 world)) (box r (p4 world))))))) (or (or (or (dia r (dia r (and (not (p5 world)) (box r (p1 world))))) (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))) (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))) false)) (or false (or (dia r (and (not (p4 world)) (box r (p6 world)))) (dia r (and (not (p6 world)) (box r (p6 world))))))) (or (or (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))) (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world))))))) false)) (or false (or (or (dia r (dia r (and (not (p2 world)) (box r (p2 world))))) (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))) (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))) (or (or (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))) (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world))))))) false)) (or false (or (or (dia r (dia r (and (not (p2 world)) (box r (p4 world))))) (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))) (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))) (or (or (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))) (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world))))))) false)) (or (dia r (dia r (dia r (and (not (p6 world)) (box r (p5 world)))))) (or (or (dia r (dia r (and (not (p2 world)) (box r (p6 world))))) (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))) (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))) (or (or (or (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))) (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))) (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))) false)) (or false (or (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))) (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))) (or (or (or (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))) (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))) (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))) false)) (or false (or (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))) (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))) (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))) (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p4 world)))))))) (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))) false)) (or false (or (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))) (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))) (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))) (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p3 world)))))))) (or (or (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))) (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))) (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))) (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))) (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p2 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))) (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p1 world)))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p6 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p3 world)))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p6 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p3 world)))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p6 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p3 world)))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p6 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p3 world)))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))))))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p6 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world))))))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world))))))))))))))))))))) false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world))))))))))))))))))))) false)) (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p3 world)))))))))))))))))))) (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world)))))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p1 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p3 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p1 world)) (box r (p5 world)))))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world))))))))))))))))))))))) (or (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p1 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p3 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p6 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p3 world)) (box r (p5 world)))))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world))))))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p1 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p3 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p5 world)) (box r (p5 world)))))))))))))))))))))) false)) (or false (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world)))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world))))))))))))))))))))))) (or false false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p2 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p2 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p2 world)))))))))))))))))))))))) (or false false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p4 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p4 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p4 world)))))))))))))))))))))))) (or false false)) (or false (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p2 world)) (box r (p6 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p4 world)) (box r (p6 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (and (not (p6 world)) (box r (p6 world))))))))))))))))))))))))) (or (or (or (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (not (p2 world))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (not (p4 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (not (p6 world)))))))))))))))))))))) (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (dia r (not (p6 world)))))))))))))))))))))))))
