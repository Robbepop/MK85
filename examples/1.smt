; [Prove that] For any integers m and n, if 7m+5n=147, then m is odd or n is odd.
; https://math.stackexchange.com/questions/519865/any-universal-or-existential-quantifier
; https://courses.engr.illinois.edu/cs173/fa2009/Homework/hw3_solutions.pdf

; we do this only for 32-bit m,n.

(declare-fun m () (_ BitVec 32))
(declare-fun n () (_ BitVec 32))

; be sure both m and n are even:

(assert (and
	(= (bvand m #xFFFFFFFE) #x00000000)
	(= (bvand n #xFFFFFFFE) #x00000000)
))

; 7m+5n=147

(assert (=
	(bvadd 
		(bvmul_no_overflow m (_ bv7 32))
		(bvmul_no_overflow n (_ bv5 32))
	)
	(_ bv147 32)
))

; find even m, n for the equation. must be unsat (no m,n pair can be found)

(check-sat)
;(get-model)

