; 1959 AHSME Problems, Problem 8

; 8th problem at http://artofproblemsolving.com/wiki/index.php?title=1959_AHSME_Problems

; "The value of $x^2-6x+13$ can never be less than:
; 4, 4.5, 5, 7, 13"
; 
; must be x=3, result=4, see also: https://www.wolframalpha.com/input/?i=minimize+x*x-6x%2B13+over+[-100,100]

(declare-fun x () (_ BitVec 16))
(declare-fun result () (_ BitVec 16))

(assert (= 
	((_ zero_extend 16) result) 
	(bvadd 
		(bvsub 
			(bvmul ((_ zero_extend 16) x) ((_ zero_extend 16) x)) 
			(bvmul ((_ zero_extend 16) x) #x00000006))
		#x0000000d))
)
(minimize result)

(check-sat)
(get-model)

; correct result:
;(model
;        (define-fun x () (_ BitVec 16) (_ bv3 16)) ; 0x3
;        (define-fun result () (_ BitVec 16) (_ bv4 16)) ; 0x4
;)

