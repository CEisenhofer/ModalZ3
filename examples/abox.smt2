(declare-const p (World) Bool)
(declare-const q (World) Bool)
(declare-const w1 World)
(declare-const w2 World)
(declare-const r1 Relation)

(assert (global (p w1) (dia r1 p))) ; w1 [p] -> w3 [p] ; simplifies to (=> (p w1) (dia r1 p)) 
(assert (not (p w2))) ; w2 [!p]
(assert (global (not (p world)) (q world))) ; maybe instead (global (not (p current)) (dia r1 (not (p current)))) remove q
