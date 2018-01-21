; must be 12
; see also example using z3: https://yurichev.com/blog/LCM/

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun LCM () (_ BitVec 8))

(assert (bvugt LCM #x00))
(assert (= (bvmul ((_ zero_extend 8) x) (_ bv4 16)) ((_ zero_extend 8) LCM)))
(assert (= (bvmul ((_ zero_extend 8) y) (_ bv6 16)) ((_ zero_extend 8) LCM)))
(minimize LCM)

(check-sat)
(get-model)

; correct result:
;(model
;        (define-fun x () (_ BitVec 8) (_ bv3 8)) ; 0x3
;        (define-fun y () (_ BitVec 8) (_ bv2 8)) ; 0x2
;        (define-fun LCM () (_ BitVec 8) (_ bv12 8)) ; 0xc
;)

