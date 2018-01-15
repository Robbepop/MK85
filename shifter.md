# Making (almost) barrel shifter in my toy-level SMT solver

... so the functions "bvshl" and "bvlshr" (logical shift right) would be supported.

We will simulate barrel shifter, a device which can shift a value by several bits in one cycle.
This one is one nice illustration:
https://i.stack.imgur.com/AefYE.jpg

See also: https://en.wikipedia.org/wiki/Barrel_shifter

So we have a pack of multiplexers. a tier of them for each bit in "cnt" variable (number of bits to shift).

First, I define functions which do "rewiring" rather than shifting, it's just another name.
Part of input is "connected" to output bits, other bits are fixed to zero:

	// "cnt" is not a SMT variable!
	struct SMT_var* generate_shift_left(struct SMT_var* X, unsigned int cnt)
	{
		int w=X->width;

		struct SMT_var* rt=create_internal_variable("shifted_left", TY_BITVEC, w);

		fix_BV_to_zero(rt->SAT_var, cnt);

		add_Tseitin_EQ_bitvecs(w-cnt, rt->SAT_var+cnt, X->SAT_var);

		return rt;
	};

	// cnt is not a SMT variable!
	struct SMT_var* generate_shift_right(struct SMT_var* X, unsigned int cnt)
	{
		... likewise
	};

It can be said, the "cnt" variable would be set during SAT instance creation, but it cannot be changed during solving.

Now let's create a "real" shifter.
Now for 8-bit left shifter, I'm generating the following (long) expression:

	X=ITE(cnt&1, X<<1, X)
	X=ITE((cnt>>1)&1, X<<2, X)
	X=ITE((cnt>>2)&1, X<<4, X)

I.e., if a specific bit is set in "cnt", shift X by that ammount of bits, or do nothing otherwise.
ITE() is a if-then-else gate, works for bitvectors as well.

Glueling all this together:

	// direction=false for shift left
	// direction=true for shift right
	struct SMT_var* generate_shifter (struct SMT_var* X, struct SMT_var* cnt, bool direction)
	{
		int w=X->width;

		struct SMT_var* in=X;
		struct SMT_var* out;
		struct SMT_var* tmp;

		// bit vector must have width=2^x, i.e., 8, 16, 32, 64, etc
		assert (popcount64c (w)==1);

		int bits_in_selector=mylog2(w);

		for (int i=0; i<bits_in_selector; i++)
		{
			if (direction==false)
				tmp=generate_shift_left(in, 1<<i);
			else
				tmp=generate_shift_right(in, 1<<i);

			out=create_internal_variable("tmp", TY_BITVEC, w);

			add_Tseitin_ITE_BV (cnt->SAT_var+i, tmp->SAT_var, in->SAT_var, out->SAT_var, w);

			in=out;
		};

		// if any bit is set in high part of "cnt" variable, result is 0
		// i.e., if a 8-bit bitvector is shifted by cnt>8, give a zero
		struct SMT_var *disable_shifter=create_internal_variable("...", TY_BOOL, 1);
		add_Tseitin_OR_list(cnt->SAT_var+bits_in_selector, w-bits_in_selector, disable_shifter->SAT_var);

		return generate_ITE(disable_shifter, generate_const(0, w), in);
	};

	struct SMT_var* generate_BVSHL (struct SMT_var* X, struct SMT_var* cnt)
	{
		return generate_shifter (X, cnt, false);
	};

Now the puzzle.
a>>b must be equal to 0x12345678, while several bits in "a" must be reset, like (a&0xf1110100)==0.
Find a, b:

	(declare-fun a () (_ BitVec 32))
	(declare-fun b () (_ BitVec 32))

	(assert (= (bvand a #xf1110100) #x00000000))

	(assert (= (bvshl a b) #x12345678))

	(check-sat)
	(get-model)

The solution:

	sat
	(model
	        (define-fun a () (_ BitVec 32) (_ bv38177487 32)) ; 0x2468acf
        	(define-fun b () (_ BitVec 32) (_ bv3 32)) ; 0x3
	)

