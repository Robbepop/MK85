; http://artofproblemsolving.com/wiki/index.php?title=2015_AIME_II_Problems/Problem_12
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 10))

(declare-fun mask () (_ BitVec 10))
(assert (= mask (_ bv15 10)))

(declare-fun zero () (_ BitVec 10))
(assert (= zero (_ bv0 10)))

(declare-fun shifted0 () (_ BitVec 10))
(assert (= shifted0 (bvand a mask)))

(declare-fun shifted1 () (_ BitVec 10))
(assert (= shifted1 (bvand (bvlshr a (_ bv1 10)) mask)))

(declare-fun shifted2 () (_ BitVec 10))
(assert (= shifted2 (bvand (bvlshr a (_ bv2 10)) mask)))

(declare-fun shifted3 () (_ BitVec 10))
(assert (= shifted3 (bvand (bvlshr a (_ bv3 10)) mask)))

(declare-fun shifted4 () (_ BitVec 10))
(assert (= shifted4 (bvand (bvlshr a (_ bv4 10)) mask)))

(declare-fun shifted5 () (_ BitVec 10))
(assert (= shifted5 (bvand (bvlshr a (_ bv5 10)) mask)))

(declare-fun shifted6 () (_ BitVec 10))
(assert (= shifted6 (bvand (bvlshr a (_ bv6 10)) mask)))

(assert (and (not (= shifted0 zero)) (not (= shifted0 mask))))
(assert (and (not (= shifted1 zero)) (not (= shifted1 mask))))
(assert (and (not (= shifted2 zero)) (not (= shifted2 mask))))
(assert (and (not (= shifted3 zero)) (not (= shifted3 mask))))
(assert (and (not (= shifted4 zero)) (not (= shifted4 mask))))
(assert (and (not (= shifted5 zero)) (not (= shifted5 mask))))
(assert (and (not (= shifted6 zero)) (not (= shifted6 mask))))

;(check-sat)
;(get-model)
;(get-all-models)
(count-models)

