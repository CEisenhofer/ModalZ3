; Seed: 299828338
(declare-const r1 Relation)

(declare-fun p (World) Bool)
(declare-fun q (World) Bool)

(assert (not (or (q world) (not (box r1 (not (p world)))))))

; Verification failure:
;   (not (or (q world) (not (box r1 (not (p world))))))
; "Model":
; Relation r1:
;
; q:
;         w0: false
;
; p:
