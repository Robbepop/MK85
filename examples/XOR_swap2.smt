; prove that XOR swap algorithm (using addition/subtraction) is correct.
; https://en.wikipedia.org/wiki/XOR_swap_algorithm

; initial: X1, Y1
;X2 := X1 ADD Y1
;Y3 := X2 SUB Y1
;X4 := X2 SUB Y3
; prove X1=Y3 and Y1=X4 for all

; must be unsat, of course

; needless to say that other SMT solvers may use simplification to prove this, MK85 can't do it,
; it "proves" on SAT level, by absence of counterexample to the expressions.

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x1 () (_ BitVec 32))
(declare-fun y1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun y3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))

(assert (= x2 (bvadd x1 y1)))
(assert (= y3 (bvsub x2 y1)))
(assert (= x4 (bvsub x2 y3)))

(assert (not (and (= x4 y1) (= y3 x1))))

(check-sat)

