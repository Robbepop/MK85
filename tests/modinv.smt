; find modulo inverse
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun m () (_ BitVec 16))
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))

(assert (= a (bvudiv #xa236 #x0003)))
(assert (= b (bvmul #xa236 m)))

(assert (= a b))

; without this constraint, two results would be generated (with MSB=1 and MSB=0), but we need only one
; indeed, MSB of m has no effect of multiplication here and SMT-solver offers two solutions
(assert (= (bvand m #x8000) #x0000))

(check-sat)
(get-model)
;(get-all-models)

