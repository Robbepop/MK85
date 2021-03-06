; must be unsat
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun p () Bool)
(declare-fun q () Bool)

(declare-fun out1 () Bool)
(declare-fun out2 () Bool)

(assert (=(not (and p q)) out1))
(assert (=(or (not p) (not q)) out2))

(assert (not (= out1 out2)))

(check-sat)
(get-model)

