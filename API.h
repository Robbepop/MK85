// visible to API users

#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

enum TY
{
	TY_BOOL=0,
	TY_BITVEC=1
};

enum OP
{
	OP_NOT=0,
	OP_BVSHL=1,
	OP_BVLSHR=2,
	OP_BVASHR=3,
	OP_BVSHL1=4,
	OP_BVSHR1=5,
	OP_EQ=6,
	OP_NEQ=7,
	OP_AND=8,
	OP_OR=9,
	OP_XOR=10,
	OP_BVNOT=11,
	OP_BVNEG=12,
	OP_BVXOR=13,
	OP_BVADD=14,
	OP_BVAND=15,
	OP_BVOR=16,
	OP_BVMUL=17,
	OP_BVMUL_NO_OVERFLOW=18,
	OP_BVSUB=19,
	OP_BVUGE=20,
	OP_BVUGT=21,
	OP_BVULE=22,
	OP_BVULT=23,
	OP_BVSGE=24,
	OP_BVSGT=25,
	OP_BVSLE=26,
	OP_BVSLT=27,
	OP_BVSUBGE=28,
	OP_BVUDIV=29,
	OP_BVUREM=30,
	OP_ITE=31
};

void set_verbose(int level);
struct ctx* MK85_init();
struct expr* create_id(struct ctx* ctx, char* id);
struct expr* create_unary_expr(enum OP t, struct expr* op);
struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2);
struct expr* create_ternary_expr(enum OP t, struct expr* op1, struct expr* op2, struct expr* op3);
struct expr* create_vararg_expr(enum OP t, struct expr* args);
struct expr* create_distinct_expr(struct expr* args);
struct expr* create_const_expr(uint32_t c, int w);
struct expr* create_zero_extend_expr(int bits, struct expr* e);
struct expr* create_repeat_expr(int times, struct expr* e);
struct expr* create_extract_expr(unsigned end, unsigned start, struct expr* e);
enum TY get_type_of_expr(struct expr*);
int get_width_of_expr(struct expr*);
char * expr_to_string(struct expr* e);

// DIRTY HACK!
// rationale: encapsulate "struct expr" details from API users
struct expr* set_next(struct expr* arg, struct expr* n);

struct SMT_var* declare_variable(struct ctx* ctx, const char* name, enum TY type, int width, int internal);
void create_assert (struct ctx* ctx, struct expr* e);
void create_min_max (struct ctx* ctx, struct expr* e, int min_max);

// return type - bool
int check_sat(struct ctx* ctx);

uint32_t get_variable_val(struct ctx* ctx, char* id);

#ifdef __cplusplus
}
#endif

