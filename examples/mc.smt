; https://yurichev.com/blog/MC_puzzle/
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)

(assert (= a (and b c d e f)))
(assert (= b (and (not c) (not d) (not e) (not f))))
(assert (= c (and a b)))
(assert (= d (or 
	(and a (not b) (not c))
	(and (not a) b (not c))
	(and (not a) (not b) c)
	)))
(assert (= e (and (not a) (not b) (not c) (not d))))
(assert (= f (and (not a) (not b) (not c) (not d) (not e))))

(check-sat)
(get-model)

