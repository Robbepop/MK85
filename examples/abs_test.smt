; prove that branchless abs() function from Henry Warren 2ed, "2-4 Absolute Value Function" is correct.

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 32))

; result1=abs(x), my version:
(declare-fun result1 () (_ BitVec 32))

(assert (= result1 (ite (bvslt x #x00000000) (bvneg x) x)))

; from Henry Warren book.
; y = x>>s 31
; result2=(x xor y) - y
(declare-fun y () (_ BitVec 32))
(declare-fun result2 () (_ BitVec 32))

(assert (= y (bvashr x (_ bv31 32))))
(assert (= result2 (bvsub (bvxor x y) y)))

(assert (distinct result1 result2))

; must be unsat:
(check-sat)

