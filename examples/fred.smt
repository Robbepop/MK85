; https://yurichev.com/blog/fred_puzzle/
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun fg () Bool)
(declare-fun fi () Bool)
(declare-fun tg () Bool)
(declare-fun ti () Bool)
(declare-fun eg () Bool)
(declare-fun ei () Bool)

(assert (not (= fg fi)))
(assert (not (= tg ti)))
(assert (not (= eg ei)))

(assert (= ei (and fg ti)))

; Or(-x, y) is the same as Implies
(assert (= fi (or (not eg) tg)))

(assert (= ti (and ti (or fg eg))))

(check-sat)
(get-model)

