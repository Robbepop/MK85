; copypasted from http://fmv.jku.at/biere/talks/Biere-SYNASC17-talk.pdf
; must be unsat, of course

(set-logic QF_BV)
;(declare-fun x () (_ BitVec 12))
;(declare-fun y () (_ BitVec 12))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (distinct (bvmul x y) (bvmul y x)))
(check-sat)

