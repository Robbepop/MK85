; checked with Z3 and MK85

; "THE YEAR OF SOPHIE’S BIRTH
; In January 1993, Sophie’s age equaled the sum of digits comprised in her birth year. What year was Sophie born in?"
; Bartholomew Dyda and Zbigniew Romanowicz, 100 Math Brainteasers: http://ebooks.dcbooks.com/assets/preview/100-math-brainteasers.pdf

; variables:
(declare-fun birth_year () (_ BitVec 16))
(declare-fun age_in_1993 () (_ BitVec 16))

; constant we will use often:
(declare-fun ten () (_ BitVec 16))
(assert (= ten (_ bv10 16)))

; get sum of all digits in birth_year, base 10:
; age_in_1993 == (birth_year % 10) + ((birth_year / 10 ) % 10) + 9 + 1
(assert (=
	age_in_1993
	(bvadd
		(bvurem birth_year ten)
		(bvurem (bvudiv birth_year ten) ten)
		(_ bv10 16) ; 9+1
	)
	)
)

; 1993 - age_in_1993 == birth_year
(assert (=
	birth_year
	(bvsub
		(_ bv1993 16)
		age_in_1993
	)
	)
)

(check-sat)
(get-model)

; correct result:

; sat
; (model
;        (define-fun age_in_1993 () (_ BitVec 16) (_ bv20 16)) ; 0x14
;        (define-fun birth_year () (_ BitVec 16) (_ bv1973 16)) ; 0x7b5
;        (define-fun ten () (_ BitVec 16) (_ bv10 16)) ; 0xa
; )

; so she was born in 1973

