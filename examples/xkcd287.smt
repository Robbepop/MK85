; https://yurichev.com/blog/xkcd287/

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(declare-fun e () (_ BitVec 16))
(declare-fun f () (_ BitVec 16))

(assert (bvult a #x0010))
(assert (bvult b #x0010))
(assert (bvult c #x0010))
(assert (bvult d #x0010))
(assert (bvult e #x0010))
(assert (bvult f #x0010))

(assert 
	(= 
		(bvadd
			(bvmul (_ bv215 16) a)
			(bvmul (_ bv275 16) b)
			(bvmul (_ bv335 16) c)
			(bvmul (_ bv355 16) d)
			(bvmul (_ bv420 16) e)
			(bvmul (_ bv580 16) f)
		)
		(_ bv1505 16)
	)
)

;(check-sat)
;(get-model)
(get-all-models)

