; (declare-sort Relation 0)
; (declare-sort World 0)

(declare-const r1 Relation)

(declare-fun p (World) Bool)

(assert (box r1 (box r1 (or (not (p world)) (p world)))))

; (declare-fun Var!1807 (World) Bool)
; 
; (declare-fun world!1825 () World)
; (declare-fun world!1824 () World)
; (declare-fun world!1826 () World)
; 
; (declare-fun reachable (Relation World World) Bool)
; 
; (assert
;     (forall ((world!1825 World))
;     	(=> (reachable r1 world!1824 world!1825) 
;     	    (forall ((world!1826 World))
;     	        (=> (reachable r1 world!1825 world!1826)
;     			    (or (not (Var!1807 world!1826)) (Var!1807 world!1826))
;     			)
;             )
;         )
;     )
; )
; 
; (check-sat)
; (get-model)
; 