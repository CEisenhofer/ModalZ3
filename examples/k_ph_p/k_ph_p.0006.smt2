(declare-const r Relation)
(declare-fun p101 (World) Bool)
(declare-fun p102 (World) Bool)
(declare-fun p103 (World) Bool)
(declare-fun p104 (World) Bool)
(declare-fun p105 (World) Bool)
(declare-fun p106 (World) Bool)
(declare-fun p201 (World) Bool)
(declare-fun p202 (World) Bool)
(declare-fun p203 (World) Bool)
(declare-fun p204 (World) Bool)
(declare-fun p205 (World) Bool)
(declare-fun p206 (World) Bool)
(declare-fun p301 (World) Bool)
(declare-fun p302 (World) Bool)
(declare-fun p303 (World) Bool)
(declare-fun p304 (World) Bool)
(declare-fun p305 (World) Bool)
(declare-fun p306 (World) Bool)
(declare-fun p401 (World) Bool)
(declare-fun p402 (World) Bool)
(declare-fun p403 (World) Bool)
(declare-fun p404 (World) Bool)
(declare-fun p405 (World) Bool)
(declare-fun p406 (World) Bool)
(declare-fun p501 (World) Bool)
(declare-fun p502 (World) Bool)
(declare-fun p503 (World) Bool)
(declare-fun p504 (World) Bool)
(declare-fun p505 (World) Bool)
(declare-fun p506 (World) Bool)
(declare-fun p601 (World) Bool)
(declare-fun p602 (World) Bool)
(declare-fun p603 (World) Bool)
(declare-fun p604 (World) Bool)
(declare-fun p605 (World) Bool)
(declare-fun p606 (World) Bool)
(declare-fun p701 (World) Bool)
(declare-fun p702 (World) Bool)
(declare-fun p703 (World) Bool)
(declare-fun p704 (World) Bool)
(declare-fun p705 (World) Bool)
(declare-fun p706 (World) Bool)
(assert (not (=> (dia r (and (and (and (and (and (and (or (or (or (or (or (p101 world) (box r (p102 world))) (box r (p103 world))) (box r (p104 world))) (box r (p105 world))) (box r (p106 world))) (or (or (or (or (or (p201 world) (p202 world)) (box r (p203 world))) (box r (p204 world))) (box r (p205 world))) (box r (p206 world)))) (or (or (or (or (or (p301 world) (p302 world)) (p303 world)) (box r (p304 world))) (box r (p305 world))) (box r (p306 world)))) (or (or (or (or (or (p401 world) (p402 world)) (p403 world)) (p404 world)) (box r (p405 world))) (box r (p406 world)))) (or (or (or (or (or (p501 world) (p502 world)) (p503 world)) (p504 world)) (p505 world)) (box r (p506 world)))) (or (or (or (or (or (p601 world) (p602 world)) (p603 world)) (p604 world)) (p605 world)) (p606 world))) (or (or (or (or (or (p701 world) (p702 world)) (p703 world)) (p704 world)) (p705 world)) (p706 world)))) (dia r (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (p101 world) (p201 world)) (and (p101 world) (p301 world))) (and (p101 world) (p401 world))) (and (p101 world) (p501 world))) (and (p101 world) (p601 world))) (and (p101 world) (p701 world))) (and (p201 world) (p301 world))) (and (p201 world) (p401 world))) (and (p201 world) (p501 world))) (and (p201 world) (p601 world))) (and (p201 world) (p701 world))) (and (p301 world) (p401 world))) (and (p301 world) (p501 world))) (and (p301 world) (p601 world))) (and (p301 world) (p701 world))) (and (p401 world) (p501 world))) (and (p401 world) (p601 world))) (and (p401 world) (p701 world))) (and (p501 world) (p601 world))) (and (p501 world) (p701 world))) (and (p601 world) (p701 world))) (and (box r (p102 world)) (p202 world))) (and (box r (p102 world)) (p302 world))) (and (box r (p102 world)) (p402 world))) (and (box r (p102 world)) (p502 world))) (and (box r (p102 world)) (p602 world))) (and (box r (p102 world)) (p702 world))) (and (p202 world) (p302 world))) (and (p202 world) (p402 world))) (and (p202 world) (p502 world))) (and (p202 world) (p602 world))) (and (p202 world) (p702 world))) (and (p302 world) (p402 world))) (and (p302 world) (p502 world))) (and (p302 world) (p602 world))) (and (p302 world) (p702 world))) (and (p402 world) (p502 world))) (and (p402 world) (p602 world))) (and (p402 world) (p702 world))) (and (p502 world) (p602 world))) (and (p502 world) (p702 world))) (and (p602 world) (p702 world))) (and (box r (p103 world)) (box r (p203 world)))) (and (box r (p103 world)) (p303 world))) (and (box r (p103 world)) (p403 world))) (and (box r (p103 world)) (p503 world))) (and (box r (p103 world)) (p603 world))) (and (box r (p103 world)) (p703 world))) (and (box r (p203 world)) (p303 world))) (and (box r (p203 world)) (p403 world))) (and (box r (p203 world)) (p503 world))) (and (box r (p203 world)) (p603 world))) (and (box r (p203 world)) (p703 world))) (and (p303 world) (p403 world))) (and (p303 world) (p503 world))) (and (p303 world) (p603 world))) (and (p303 world) (p703 world))) (and (p403 world) (p503 world))) (and (p403 world) (p603 world))) (and (p403 world) (p703 world))) (and (p503 world) (p603 world))) (and (p503 world) (p703 world))) (and (p603 world) (p703 world))) (and (box r (p104 world)) (box r (p204 world)))) (and (box r (p104 world)) (box r (p304 world)))) (and (box r (p104 world)) (p404 world))) (and (box r (p104 world)) (p504 world))) (and (box r (p104 world)) (p604 world))) (and (box r (p104 world)) (p704 world))) (and (box r (p204 world)) (box r (p304 world)))) (and (box r (p204 world)) (p404 world))) (and (box r (p204 world)) (p504 world))) (and (box r (p204 world)) (p604 world))) (and (box r (p204 world)) (p704 world))) (and (box r (p304 world)) (p404 world))) (and (box r (p304 world)) (p504 world))) (and (box r (p304 world)) (p604 world))) (and (box r (p304 world)) (p704 world))) (and (p404 world) (p504 world))) (and (p404 world) (p604 world))) (and (p404 world) (p704 world))) (and (p504 world) (p604 world))) (and (p504 world) (p704 world))) (and (p604 world) (p704 world))) (and (box r (p105 world)) (box r (p205 world)))) (and (box r (p105 world)) (box r (p305 world)))) (and (box r (p105 world)) (box r (p405 world)))) (and (box r (p105 world)) (p505 world))) (and (box r (p105 world)) (p605 world))) (and (box r (p105 world)) (p705 world))) (and (box r (p205 world)) (box r (p305 world)))) (and (box r (p205 world)) (box r (p405 world)))) (and (box r (p205 world)) (p505 world))) (and (box r (p205 world)) (p605 world))) (and (box r (p205 world)) (p705 world))) (and (box r (p305 world)) (box r (p405 world)))) (and (box r (p305 world)) (p505 world))) (and (box r (p305 world)) (p605 world))) (and (box r (p305 world)) (p705 world))) (and (box r (p405 world)) (p505 world))) (and (box r (p405 world)) (p605 world))) (and (box r (p405 world)) (p705 world))) (and (p505 world) (p605 world))) (and (p505 world) (p705 world))) (and (p605 world) (p705 world))) (and (box r (p106 world)) (box r (p206 world)))) (and (box r (p106 world)) (box r (p306 world)))) (and (box r (p106 world)) (box r (p406 world)))) (and (box r (p106 world)) (box r (p506 world)))) (and (box r (p106 world)) (p606 world))) (and (box r (p106 world)) (p706 world))) (and (box r (p206 world)) (box r (p306 world)))) (and (box r (p206 world)) (box r (p406 world)))) (and (box r (p206 world)) (box r (p506 world)))) (and (box r (p206 world)) (p606 world))) (and (box r (p206 world)) (p706 world))) (and (box r (p306 world)) (box r (p406 world)))) (and (box r (p306 world)) (box r (p506 world)))) (and (box r (p306 world)) (p606 world))) (and (box r (p306 world)) (p706 world))) (and (box r (p406 world)) (box r (p506 world)))) (and (box r (p406 world)) (p606 world))) (and (box r (p406 world)) (p706 world))) (and (box r (p506 world)) (p606 world))) (and (box r (p506 world)) (p706 world))) (and (p606 world) (p706 world)))))))