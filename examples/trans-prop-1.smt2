; unsat
(declare-fun p (World) Bool)
(declare-const r1 Relation)

(assert (dia r1 ; box!1 and world!4
    (dia r1 ; world!5
        (p world))))

(assert (box r1 ; box!2
    (not (p world))))

(assert (trans r1))
