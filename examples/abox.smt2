(declare-fun p (World) Bool)
(declare-fun q (World) Bool)
(declare-const w1 World)
(declare-const w2 World)
(declare-const r1 Relation)

(assert (global (=> (or (= world w1) (= world w2)) (dia r1 (p world))))) ; w1/w2 -> w? [p]
(assert (and (global (=> (= world w1) (q world))))) ; w1 [q],
(assert (and (p w1) (p w2))) ; w1/w2 [p]
(assert (dia r1 (not (p world)))) ; w? -> w? [!p]

; Expected model:
; Initial world -> w? [!p]
; w1 [p, q] -> w? [p]
; w2 [p] -> w? [p]

