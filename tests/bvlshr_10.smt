(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 10))
(declare-fun b () (_ BitVec 10))
(declare-fun c () (_ BitVec 10))

(assert (= a (_ bv123 10)))
(assert (= b (bvlshr a (_ bv1 10))))
(assert (= c (bvshl a (_ bv1 10))))

(check-sat)
(get-model)

