; https://yurichev.com/blog/assign_method/

(declare-fun choice1 () (_ BitVec 2))
(declare-fun choice2 () (_ BitVec 2))
(declare-fun choice3 () (_ BitVec 2))

(declare-fun row_value1 () (_ BitVec 16))
(declare-fun row_value2 () (_ BitVec 16))
(declare-fun row_value3 () (_ BitVec 16))

(declare-fun final_sum () (_ BitVec 16))

(assert (bvule choice1 (_ bv3 2)))
(assert (bvule choice2 (_ bv3 2)))
(assert (bvule choice3 (_ bv3 2)))

(assert (distinct choice1 choice2 choice3))

(assert (= row_value1
	(ite (= choice1 (_ bv0 2)) (_ bv250 16)
	(ite (= choice1 (_ bv1 2)) (_ bv400 16)
	(ite (= choice1 (_ bv2 2)) (_ bv250 16)
	(_ bv999 16))))))

(assert (= row_value2
	(ite (= choice2 (_ bv0 2)) (_ bv400 16)
	(ite (= choice2 (_ bv1 2)) (_ bv600 16)
	(ite (= choice2 (_ bv2 2)) (_ bv350 16)
	(_ bv999 16))))))

(assert (= row_value3
	(ite (= choice3 (_ bv0 2)) (_ bv200 16)
	(ite (= choice3 (_ bv1 2)) (_ bv400 16)
	(ite (= choice3 (_ bv2 2)) (_ bv250 16)
	(_ bv999 16))))))

(assert (= final_sum (bvadd row_value1 row_value2 row_value3)))

(minimize final_sum)

(check-sat)
(get-model)
; correct result:

;(model
;        (define-fun choice1 () (_ BitVec 2) (_ bv1 2)) ; 0x1
;        (define-fun choice2 () (_ BitVec 2) (_ bv2 2)) ; 0x2
;        (define-fun choice3 () (_ BitVec 2) (_ bv0 2)) ; 0x0
;        (define-fun row_value1 () (_ BitVec 16) (_ bv400 16)) ; 0x190
;        (define-fun row_value2 () (_ BitVec 16) (_ bv350 16)) ; 0x15e
;        (define-fun row_value3 () (_ BitVec 16) (_ bv200 16)) ; 0xc8
;        (define-fun final_sum () (_ BitVec 16) (_ bv950 16)) ; 0x3b6
;)

