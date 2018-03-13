; https://ru.wikipedia.org/wiki/%D0%A1%D1%87%D0%B0%D1%81%D1%82%D0%BB%D0%B8%D0%B2%D1%8B%D0%B9_%D0%B1%D0%B8%D0%BB%D0%B5%D1%82
; http://www.genfunc.ru/theory/lucky/
(declare-fun n1 () (_ BitVec 8))
(declare-fun n2 () (_ BitVec 8))
(declare-fun n3 () (_ BitVec 8))
(declare-fun n4 () (_ BitVec 8))
(declare-fun n5 () (_ BitVec 8))
(declare-fun n6 () (_ BitVec 8))

(assert (and (bvuge n1 #x00) (bvule n1 #x09)))
(assert (and (bvuge n2 #x00) (bvule n2 #x09)))
(assert (and (bvuge n3 #x00) (bvule n3 #x09)))
(assert (and (bvuge n4 #x00) (bvule n4 #x09)))
(assert (and (bvuge n5 #x00) (bvule n5 #x09)))
(assert (and (bvuge n6 #x00) (bvule n6 #x09)))

(declare-fun sum1 () (_ BitVec 8))
(assert (= sum1 (bvadd n1 n2 n3)))

(declare-fun sum2 () (_ BitVec 8))
(assert (= sum2 (bvadd n4 n5 n6)))

(assert (= sum1 sum2))

;(check-sat)
;(get-model)
;(get-all-models)
(count-models)

; correct answer:
; Model count: 55252

