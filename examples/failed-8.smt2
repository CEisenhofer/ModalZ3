(declare-const r1 Relation)

(declare-fun p (World) Bool)

(assert
    (or (not (box r1 (box r1 (or (not (p world)) (p world))))) (p world))
)

; (assert
;     (p world)
; )
