(declare-fun p (World) Bool)
(declare-const r1 Relation)
(assert (global true)) ; Should be killed by simplifier
(assert (global (dia r1 (and (p world) (dia r1 (not (p world)))))))
; (assert (global (dia r1 true)))
