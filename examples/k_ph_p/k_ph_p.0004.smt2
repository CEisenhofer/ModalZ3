(declare-const r Relation)
(declare-fun p101 (World) Bool)
(declare-fun p102 (World) Bool)
(declare-fun p103 (World) Bool)
(declare-fun p104 (World) Bool)
(declare-fun p201 (World) Bool)
(declare-fun p202 (World) Bool)
(declare-fun p203 (World) Bool)
(declare-fun p204 (World) Bool)
(declare-fun p301 (World) Bool)
(declare-fun p302 (World) Bool)
(declare-fun p303 (World) Bool)
(declare-fun p304 (World) Bool)
(declare-fun p401 (World) Bool)
(declare-fun p402 (World) Bool)
(declare-fun p403 (World) Bool)
(declare-fun p404 (World) Bool)
(declare-fun p501 (World) Bool)
(declare-fun p502 (World) Bool)
(declare-fun p503 (World) Bool)
(declare-fun p504 (World) Bool)
(assert (not (=> (dia r (and (and (and (and (or (or (or (p101 world) (box r (p102 world))) (box r (p103 world))) (box r (p104 world))) (or (or (or (p201 world) (p202 world)) (box r (p203 world))) (box r (p204 world)))) (or (or (or (p301 world) (p302 world)) (p303 world)) (box r (p304 world)))) (or (or (or (p401 world) (p402 world)) (p403 world)) (p404 world))) (or (or (or (p501 world) (p502 world)) (p503 world)) (p504 world)))) (dia r (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (p101 world) (p201 world)) (and (p101 world) (p301 world))) (and (p101 world) (p401 world))) (and (p101 world) (p501 world))) (and (p201 world) (p301 world))) (and (p201 world) (p401 world))) (and (p201 world) (p501 world))) (and (p301 world) (p401 world))) (and (p301 world) (p501 world))) (and (p401 world) (p501 world))) (and (box r (p102 world)) (p202 world))) (and (box r (p102 world)) (p302 world))) (and (box r (p102 world)) (p402 world))) (and (box r (p102 world)) (p502 world))) (and (p202 world) (p302 world))) (and (p202 world) (p402 world))) (and (p202 world) (p502 world))) (and (p302 world) (p402 world))) (and (p302 world) (p502 world))) (and (p402 world) (p502 world))) (and (box r (p103 world)) (box r (p203 world)))) (and (box r (p103 world)) (p303 world))) (and (box r (p103 world)) (p403 world))) (and (box r (p103 world)) (p503 world))) (and (box r (p203 world)) (p303 world))) (and (box r (p203 world)) (p403 world))) (and (box r (p203 world)) (p503 world))) (and (p303 world) (p403 world))) (and (p303 world) (p503 world))) (and (p403 world) (p503 world))) (and (box r (p104 world)) (box r (p204 world)))) (and (box r (p104 world)) (box r (p304 world)))) (and (box r (p104 world)) (p404 world))) (and (box r (p104 world)) (p504 world))) (and (box r (p204 world)) (box r (p304 world)))) (and (box r (p204 world)) (p404 world))) (and (box r (p204 world)) (p504 world))) (and (box r (p304 world)) (p404 world))) (and (box r (p304 world)) (p504 world))) (and (p404 world) (p504 world)))))))
