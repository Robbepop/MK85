(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

(assert (not(= a #x00000001)))
(assert (not(= b #x00000001)))

; 63527*63533
(assert (= (bvmul_no_overflow a b) #xf09166db))

(check-sat)
(get-model)

