(declare-fun y () Int)
(declare-fun x (World) Int)
(declare-const r Relation)

(assert (global (dia r (< (+ y (x world)) 10))))
(assert (> (+ y (x world)) 10))
(assert (> y 0))