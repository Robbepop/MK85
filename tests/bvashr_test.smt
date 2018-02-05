(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(assert (= x (bvashr #x80 (_ bv3 8))))
(assert (= y (bvashr #x80 (_ bv40 8))))

(check-sat)
(get-model)
;(get-all-models)


