// pure C

// xkcd #287 https://yurichev.com/blog/xkcd287/

// I doubt anyone would use C API, but I do this to make a bridge to Python API
// see also: https://github.com/DennisYurichev/MK85/blob/master/API.h

#include <stdio.h>
#include <assert.h>
#include "API.h"

int main()
{
	set_verbose(1);

	struct ctx* ctx=MK85_init();

	struct SMT_var* a=declare_variable(ctx, "a", TY_BITVEC, 16, 0);
	struct SMT_var* b=declare_variable(ctx, "b", TY_BITVEC, 16, 0);
	struct SMT_var* c=declare_variable(ctx, "c", TY_BITVEC, 16, 0);
	struct SMT_var* d=declare_variable(ctx, "d", TY_BITVEC, 16, 0);
	struct SMT_var* e=declare_variable(ctx, "e", TY_BITVEC, 16, 0);
	struct SMT_var* f=declare_variable(ctx, "f", TY_BITVEC, 16, 0);

	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "a"), create_const_expr(10, 16)));
	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "b"), create_const_expr(10, 16)));
	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "c"), create_const_expr(10, 16)));
	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "d"), create_const_expr(10, 16)));
	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "e"), create_const_expr(10, 16)));
	create_assert(ctx, create_bin_expr(OP_BVULT, create_id(ctx, "f"), create_const_expr(10, 16)));

	struct expr* t1=create_bin_expr(OP_BVMUL, create_id(ctx, "a"), create_const_expr(215, 16));
	struct expr* t2=create_bin_expr(OP_BVMUL, create_id(ctx, "b"), create_const_expr(275, 16));
	struct expr* t3=create_bin_expr(OP_BVMUL, create_id(ctx, "c"), create_const_expr(335, 16));
	struct expr* t4=create_bin_expr(OP_BVMUL, create_id(ctx, "d"), create_const_expr(355, 16));
	struct expr* t5=create_bin_expr(OP_BVMUL, create_id(ctx, "e"), create_const_expr(420, 16));
	struct expr* t6=create_bin_expr(OP_BVMUL, create_id(ctx, "f"), create_const_expr(580, 16));

	// form a chain out of expressions:
	set_next(t1, t2);
	set_next(t2, t3);
	set_next(t3, t4);
	set_next(t4, t5);
	set_next(t5, t6);

	create_assert(ctx, create_bin_expr(OP_EQ, create_vararg_expr(OP_BVADD, t1), create_const_expr(1505, 16)));

	while (check_sat(ctx)==1)
	{
		uint32_t solution_a=get_variable_val(ctx, "a");
		uint32_t solution_b=get_variable_val(ctx, "b");
		uint32_t solution_c=get_variable_val(ctx, "c");
		uint32_t solution_d=get_variable_val(ctx, "d");
		uint32_t solution_e=get_variable_val(ctx, "e");
		uint32_t solution_f=get_variable_val(ctx, "f");

		printf ("solution:\n");
		printf ("a=%d\n", solution_a);
		printf ("b=%d\n", solution_b);
		printf ("c=%d\n", solution_c);
		printf ("d=%d\n", solution_d);
		printf ("e=%d\n", solution_e);
		printf ("f=%d\n", solution_f);

		// block current solution:
		t1=create_bin_expr(OP_EQ, create_id(ctx, "a"), create_const_expr(solution_a, 16));
		t2=create_bin_expr(OP_EQ, create_id(ctx, "b"), create_const_expr(solution_b, 16));
		t3=create_bin_expr(OP_EQ, create_id(ctx, "c"), create_const_expr(solution_c, 16));
		t4=create_bin_expr(OP_EQ, create_id(ctx, "d"), create_const_expr(solution_d, 16));
		t5=create_bin_expr(OP_EQ, create_id(ctx, "e"), create_const_expr(solution_e, 16));
		t6=create_bin_expr(OP_EQ, create_id(ctx, "f"), create_const_expr(solution_f, 16));

		// form a chain out of expressions:
		set_next(t1, t2);
		set_next(t2, t3);
		set_next(t3, t4);
		set_next(t4, t5);
		set_next(t5, t6);

		create_assert(ctx, create_unary_expr(OP_NOT, create_vararg_expr(OP_AND, t1)));
	};
};
/*
Compilation:
	gcc API_example1.c -o API_example1 libMK85.so 

Run:
	export LD_LIBRARY_PATH=.
	
Sample output:

declare_variable(name=a, type=1, width=16, internal=0)
declare_variable(name=b, type=1, width=16, internal=0)
declare_variable(name=c, type=1, width=16, internal=0)
declare_variable(name=d, type=1, width=16, internal=0)
declare_variable(name=e, type=1, width=16, internal=0)
declare_variable(name=f, type=1, width=16, internal=0)
create_assert() (bvult a 10 (16 bits))
create_assert() (bvult b 10 (16 bits))
create_assert() (bvult c 10 (16 bits))
create_assert() (bvult d 10 (16 bits))
create_assert() (bvult e 10 (16 bits))
create_assert() (bvult f 10 (16 bits))
create_assert() (= (bvadd (bvadd (bvadd (bvadd (bvadd (bvmul f 580 (16 bits)) (bvmul e 420 (16 bits))) (bvmul d 355 (16 bits))) (bvmul c 335 (16 bits))) (bvmul b 275 (16 bits))) (bvmul a 215 (16 bits))) 1505 (16
bits))
solution:
a=7
b=0
c=0
d=0
e=0
f=0
create_assert() (not (and (and (and (and (and (= f 0 (16 bits)) (= e 0 (16 bits))) (= d 0 (16 bits))) (= c 0 (16 bits))) (= b 0 (16 bits))) (= a 7 (16 bits))))
solution:
a=1
b=0
c=0
d=2
e=0
f=1
create_assert() (not (and (and (and (and (and (= f 1 (16 bits)) (= e 0 (16 bits))) (= d 2 (16 bits))) (= c 0 (16 bits))) (= b 0 (16 bits))) (= a 1 (16 bits))))
*/

