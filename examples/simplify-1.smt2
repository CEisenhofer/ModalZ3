(declare-fun p (World) Bool)
(declare-const r Relation)

(assert (and (dia r (p world)) (p world) (not (dia r (p world)))))
(assert (and true (dia r (p world)) (and (p world) (dia r (p world)))))
(assert (or (box r (p world)) false (or (p world) (not (dia r (not (p world)))))))

; test for simplifier
