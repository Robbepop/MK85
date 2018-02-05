(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)

(assert (= a (bvslt #x01 #x02)))
(assert (= b (bvslt #x02 #x01)))
(assert (= c (bvslt #xff #xf0)))
(assert (= d (bvslt #xf0 #xff)))

(declare-fun e () Bool)
(declare-fun f () Bool)
(declare-fun g () Bool)
(declare-fun h () Bool)

(assert (= e (bvslt #xf0 #x00)))
(assert (= f (bvslt #xff #x00)))
(assert (= g (bvslt #x12 #x00)))
(assert (= h (bvslt #x7f #x00)))

(check-sat)
(get-model)

