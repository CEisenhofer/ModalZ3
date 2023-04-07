; Seed: 1268174859:
; Different results: std (sat) vs lazy-up (unsat)
(declare-const r1 Relation)
(declare-const r2 Relation)

(declare-fun p (World) Bool)
(declare-fun q (World) Bool)

(assert
    (and
    	(or
    		(not (p world))
    		(dia r2 (and (q world) (not (q world))))
    	)
    	(box r1 (not (box r2 (q world))))
    	(box r2 (q world))
    )
)

