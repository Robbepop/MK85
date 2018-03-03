; From Daniel Kroening and Ofer Strichman - Decision Procedures, An Algorithmic Point of View, 2ed

; =============================================================================================================
; Problem 2.3 (modeling: program equivalence). Show that the two if-then-else expressions below are equivalent:

; !(a || b) ? h : !(a == b) ? f : g

; !(!a || !b) ? g : (!a && !b) ? h : f

; You can assume that the variables have only one bit.
; =============================================================================================================

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun f () Bool)
(declare-fun g () Bool)
(declare-fun h () Bool)

(declare-fun out1 () Bool)
(declare-fun out2 () Bool)

(assert (=(ite (not (or a b)) h (ite (not (= a b)) f g)) out1))
(assert (=(ite (not (or (not a) (not b))) g (ite (and (not a) (not b)) h f)) out2))

; find counterexample:
(assert (distinct out1 out2))

; must be unsat (no counterexample):
(check-sat)

