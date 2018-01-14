(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))

(assert (not(= a #x0001)))
(assert (not(= b #x0001)))

(assert (= 
		(bvmul 
			((_ zero_extend 16) a) 
			((_ zero_extend 16) b)
		)
		((_ zero_extend 16) #xa25f)))

; 0xc5*0xd3 = 0xa25f

; there are two ways to factor 0xa25f, to make it works each time unchanged, make the first result less than the second:
(assert (bvult a b))

(check-sat)
(get-model)

