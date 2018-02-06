; prove that "((x+0x80000000) >>u n) - (0x80000000 >>u n)" works like arithmetical shift (bvashr function in SMT-LIB or SAR x86 instruction).
; see: Henry Warren 2ed: "2-7 Shift Right Signed from Unsigned"
; also, check if I implement signed shift right correctly:
; https://github.com/DennisYurichev/MK85/blob/834305a9851ec7976946247d42bb13d052aba005/MK85.cc#L1195
; in other words, we prove equivalence of the expression above and my implementation
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 32))
(declare-fun n () (_ BitVec 32))
(declare-fun result1 () (_ BitVec 32))
(declare-fun result2 () (_ BitVec 32))

(assert (bvule n (_ bv31 32)))

(assert (= result1 (bvashr x n)))

; ((x+0x80000000) >>u n) - (0x80000000 >>u n)
(assert (= result2
	(bvsub
		(bvlshr (bvadd x #x80000000) n)
		(bvlshr #x80000000 n)
	)
))

(assert (distinct result1 result2))

; must be unsat:
(check-sat)

