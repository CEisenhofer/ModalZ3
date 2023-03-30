(declare-const r1 Relation)
(declare-fun p (World) Bool)

(assert (=> (box r1 true) (p world)))