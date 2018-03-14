; prove that x+(y+z) = (x+y)+z
; must be unsat, of course

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (distinct 
	(bvadd x (bvadd y z))
	(bvadd (bvadd x y) z)
	)
)
(check-sat)

