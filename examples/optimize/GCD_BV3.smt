; must be 2
; see also example using z3: https://yurichev.com/blog/GCD/

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun GCD () (_ BitVec 8))

(assert (= (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) GCD)) (_ bv14 16)))
(assert (= (bvmul ((_ zero_extend 8) y) ((_ zero_extend 8) GCD)) (_ bv8 16)))
(maximize GCD)

(check-sat)
(get-model)

; correct result:
;(model
;        (define-fun x () (_ BitVec 8) (_ bv7 8)) ; 0x7
;        (define-fun y () (_ BitVec 8) (_ bv4 8)) ; 0x4
;        (define-fun GCD () (_ BitVec 8) (_ bv2 8)) ; 0x2
;)

