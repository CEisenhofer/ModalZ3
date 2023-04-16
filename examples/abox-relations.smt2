(declare-fun p (World) Bool)
(declare-fun q (World) Bool)
(declare-const w1 World)
(declare-const w2 World)
(declare-const r1 Relation)
(declare-const r2 Relation)

(assert
    (or
        (reachable r1 w1 w2)
        (reachable r2 w2 w1)
    )
)
(assert (p w2))
(assert (global (box r1 (not (p world)))))
