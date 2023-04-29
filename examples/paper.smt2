(declare-fun Hum (World) Bool) 
(declare-fun Rob (World) Bool)
(declare-fun Dr (World) Bool)
(declare-const minAge Int)   (declare-fun age (World) Int)
(declare-const max World)    (declare-const paul World)
(declare-const anc Relation) (declare-const fr Relation)

(assert (global 
    (=> (Hum world) 
        (box anc (and 
            (=> (Dr world) (>= (age world) minAge))
            (dia anc (Hum world)))))))
(assert (Hum max))
(assert (global (=> (= world max) (dia fr (Rob world)))))
(assert (reachable anc max paul))
; (assert (trans anc))