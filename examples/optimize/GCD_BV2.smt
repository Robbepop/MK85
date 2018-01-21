; must be 21
; https://www.wolframalpha.com/input/?i=GCD[861,3969,840]
; see also example using z3: https://yurichev.com/blog/GCD/

(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 16))
(declare-fun GCD () (_ BitVec 16))

(assert (= (bvmul ((_ zero_extend 16) x) ((_ zero_extend 16) GCD)) (_ bv861 32)))
(assert (= (bvmul ((_ zero_extend 16) y) ((_ zero_extend 16) GCD)) (_ bv3969 32)))
(assert (= (bvmul ((_ zero_extend 16) z) ((_ zero_extend 16) GCD)) (_ bv840 32)))

(maximize GCD)

(check-sat)
(get-model)

; correct result:
;(model
;        (define-fun x () (_ BitVec 16) (_ bv41 16)) ; 0x29
;        (define-fun y () (_ BitVec 16) (_ bv189 16)) ; 0xbd
;        (define-fun z () (_ BitVec 16) (_ bv40 16)) ; 0x28
;        (define-fun GCD () (_ BitVec 16) (_ bv21 16)) ; 0x15
;)

