; sat
(declare-const r1 Relation)
(declare-const w1 World)
(declare-const w2 World)
(declare-const w3 World)
(declare-const w4 World)

(assert (reachable r1 w1 w2))
(assert (reachable r1 w2 w3))
(assert (reachable r1 w3 w4))
(assert (reachable r1 w1 w4))
(assert (trans r1))
