; Seed: 3822994259
(declare-const r1 Relation)
(declare-const r3 Relation)

(declare-fun p (World) Bool)

(assert
    (and
        (dia r1 (p world)) ; (box!0 world!3) = false = 7 ; (p world!4) = true = 8
        (or
            (box r1 false) ; (box!1 world!3) = true = 2
            (box r3 (not (p world))) ; (box!2 world!3) = false = 5
        )
    )
)
