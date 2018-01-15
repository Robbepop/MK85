(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

(assert (= (bvand a #xf1110100) #x00000000))

(assert (= (bvshl a b) #x12345678))

(check-sat)
(get-model)

