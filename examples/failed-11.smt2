; k_t4p_p.0001
(declare-const r Relation)

(assert (not (box r (box r false))))
(assert
    (box r
        (or
            (box r false)
            (not (box r (not (box r false))))
        )
    )
)
(assert (not (box r false)))
(assert (box r (box r (not (box r false)))))


; final line - Conflict:
;(dia r ; box!7 [v7]
;	(box r false)
;
; is "false" in w1 (world!11)
; but
;
; (box r ; box!4 [v4]
;	(dia r true) ; box!5
; )
; is true in w1
; => Relevancy propagation failed
;
; Log:
;Final check : 4
;
;Current state: **World w0**:
;Const: world!10
;Aux: true
;Parent: null
;Abstract: a0
;Template: (not (and (not (box!0 (:var 0)))
;          (box!1 (:var 0))
;          (not (box!2 (:var 0)))
;          (box!3 (:var 0))))
;
;Reachable:
;via r0: w1 [(box!0 world!10)]
;via r0: w2 [(box!2 world!10)]
;
;Spread:
;via r0: a2 [(box!1 world!10)] Templ.: (or (box!6 (:var 0)) (not (box!7 (:var 0))))
;via r0: a4 [(box!3 world!10)] Templ.: (box!4 (:var 0))
;
;Assignment:
;v0: 0
;v1: 1
;v2: 0
;v3: 1
;
;**World w1**:
;Const: world!11
;Aux: (box!0 world!10)
;Parent: 0
;Abstract: a1
;Template: (not (box!9 (:var 0)))
;
;Reachable:
;
;Spread:
;
;Assignment:
;v4: 1
;v7: 0
;v9: 0
;
;<----
;Adding: removed init-info a8 justified by (box!7 world!11) with parent w1
;Recreated: w3 internally world!13 because of (not (box!7 world!11))
;Adding: created world w3 with aux (box!7 world!11) and world!13 reachable from w1 via relation r0
;Propagating (SK): (not (box!7 world!11)) => (not (not (box!8 world!13))); internally: 14 (bool_var)
;<----
;
;Adding: removed init-info a7 justified by (box!6 world!12) with parent w2
;Adding: added that a7 will spread to all children of w2 (world!12) via relation r0
;Adding: removed init-info a8 justified by (box!7 world!12) with parent w2
;Adding: added that a8 will spread to all children of w2 (world!12) via relation r0
;Adding: removed init-info a6 justified by (box!5 world!15) with parent w5
;Recreated: w6 internally world!16 because of (not (box!5 world!15))
;Adding: created world w6 with aux (box!5 world!15) and world!16 reachable from w5 via relation r0
;Propagating (SK): No propagation required; body trivial
;Adding: removed init-info a5 justified by (box!4 world!12) with parent w2
;Adding: added that a5 will spread to all children of w2 (world!12) via relation r0
;Adding: removed init-info a5 justified by (box!4 world!11) with parent w1
;
;<----
;Adding: added that a5 will spread to all children of w1 (world!11) via relation r0
;Propagating (SP): (not (box!7 world!11)) && (box!4 world!11) => (not (box!5 world!13))
;<----
;
;Adding: removed init-info a10 justified by (box!9 world!11) with parent w1
;Recreated: w5 internally world!15 because of (not (box!9 world!11))
;Adding: created world w5 with aux (box!9 world!11) and world!15 reachable from w1 via relation r0
;Propagating (SK): No propagation required; body trivial
;Propagating (SP): (not (box!9 world!11)) && (box!4 world!11) => (not (box!5 world!15))
;SAT:
;Relation r:
;	w0 -> w1
;	w0 -> w2
;	w1 -> w3
;	w1 -> w5
;	w5 -> w6
