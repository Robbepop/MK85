; must be 3
; see also example using z3: https://yurichev.com/blog/GCD/

(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 16))
(declare-fun GCD () (_ BitVec 16))

(assert (= (bvmul ((_ zero_extend 16) x) ((_ zero_extend 16) GCD)) (_ bv300 32)))
(assert (= (bvmul ((_ zero_extend 16) y) ((_ zero_extend 16) GCD)) (_ bv900 32)))
(assert (= (bvmul ((_ zero_extend 16) z) ((_ zero_extend 16) GCD)) (_ bv333 32)))
(maximize GCD)

(check-sat)
(get-model)

; correct result:
;(model
;        (define-fun x () (_ BitVec 16) (_ bv100 16)) ; 0x64
;        (define-fun y () (_ BitVec 16) (_ bv300 16)) ; 0x12c
;        (define-fun z () (_ BitVec 16) (_ bv111 16)) ; 0x6f
;        (define-fun GCD () (_ BitVec 16) (_ bv3 16)) ; 0x3
;)

