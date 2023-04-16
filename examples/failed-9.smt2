(declare-const r1 Relation)

(declare-fun p (World) Bool)
(declare-fun q (World) Bool)
(declare-fun r (World) Bool)
(declare-fun s (World) Bool)

(assert
    (or
        (box r1 false)
        (and
            (or (not (p world)) (p world))
            (q world)
            (box r1 (r world))
            (dia r1 (s world))
        )
    )
)
