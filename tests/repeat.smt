(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 8))

(assert (= a ((_ repeat 4) #x34)))
(assert (= b ((_ repeat 8) (_ bv1 1))))

(check-sat)
(get-model)
;(count-models)
;(get-all-models)

