(declare-fun p (World) Bool)
(declare-fun q (World) Bool)
(declare-const r1 Relation)
(declare-const r2 Relation)

(assert (and
    (box r1 false)
    (p world)
    (box r2 (not (p world)))
    (box r1 (p world))
    (box r2 (q world))
    (not (box r2 (p world))) ; don' merge in this
))

(assert (or
    (dia r1 (p world))
    (not (dia r1 (not (p world)))) ; don' merge in this
    (dia r1 (q world))
))

; test for simplifier
