; prove that x+x = 2x
; must be unsat, of coursee

(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(assert (distinct (bvadd x x) (bvmul x #x00000002)))
(check-sat)

