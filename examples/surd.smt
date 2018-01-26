; find x,y for x^y==19487171
; correct result x=11, y=7
; it's like http://reference.wolfram.com/language/ref/Surd.html

; non-standard function bvmul_no_overflow is used here. it behaves like bvmul, but high part is forced to be zero
; this is not like most programming languages and CPUs do division 
; (the result there is usually modulo 2^n, where n is width of CPU register.)
; however, thus it's simpler for me to write this all without adding additional zero_extend function.

(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 4))
(declare-fun out () (_ BitVec 32))

; like switch() or if() tree:
(assert (= out
	(ite (= y #x2) (bvmul_no_overflow x x)
	(ite (= y #x3) (bvmul_no_overflow x x x)
	(ite (= y #x4) (bvmul_no_overflow x x x x)
	(ite (= y #x5) (bvmul_no_overflow x x x x x)
	(ite (= y #x6) (bvmul_no_overflow x x x x x x)
	(ite (= y #x7) (bvmul_no_overflow x x x x x x x)
	(_ bv0 32)))))))))

(assert (= out (_ bv19487171 32)))

(check-sat)
(get-model)
;(model
;        (define-fun x () (_ BitVec 32) (_ bv11 32)) ; 0xb
;        (define-fun y () (_ BitVec 4) (_ bv7 4)) ; 0x7
;        (define-fun out () (_ BitVec 32) (_ bv19487171 32)) ; 0x12959c3
;)

