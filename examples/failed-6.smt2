; Seed: 1342825785
(declare-const r1 Relation)

(declare-fun p (World) Bool)

(assert (not (box r1 (box r1 (not (or (not (p world)) (p world)))))))
; (assert (dia r1 (dia r1 (or (not (p world)) (p world)))))

; Verification failure: (let ((a!1 (not (or (not (p world)) (p world)))))
;   (not (box r1 (box r1 a!1)))):
; "Model":
; SAT:
; Relation r1:
;         w0 -> w1
;         w1 -> w2
;
; p:
; We need to assign "p" a value - no matter which to please model-checker
