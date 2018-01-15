(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

(assert (= (bvand a #x0011001f) #x00000000))

(assert (= (bvlshr a b) #x12345678))

(check-sat)
(get-model)

