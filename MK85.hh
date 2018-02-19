#pragma once

#include <string>
#include <list>

#include <stdint.h>

enum TY
{
	TY_BOOL=0,
	TY_BITVEC=1
};

enum clause_type
{
	HARD_CLASUE,
	SOFT_CLAUSE,
	COMMENT
};

// no ctor, use this class as C union
class clause
{
public:
	enum clause_type type;
	std::string s; // if COMMENT
	uint32_t weight; // if SOFT_CLAUSE
	std::list<int> li; // if HARD_CLASUE/SOFT_CLAUSE
};

struct SMT_var
{
	enum TY type; // TY_BOOL, TY_BITVEC
	bool internal; // true for internal
	std::string id; // name
	int SAT_var; // in SAT instance
	int width; // in bits, 1 for bool
	// TODO: uint64_t? bitmap?
	uint32_t val; // what we've got from from SAT-solver's results. 0/1 for Bool
	struct expr* e;
};

struct ctx
{
	std::list<struct SMT_var*> vars;
	int SAT_next_var_no; // =1 in init()!
	int next_internal_var; // =1 in init()
	struct SMT_var* var_always_false; // NULL in init();
	struct SMT_var* var_always_true; // NULL in init();

	// global switches
	// TODO: document them
	bool dump_internal_variables;
	bool write_CNF_file;

	int clauses_t;
	std::list<class clause> clauses;

	uint32_t max_weight;
	bool maxsat;

	bool create_min_max_called;

	bool sat;
	int* solution;
};

enum OP
{
	OP_NOT,
	OP_BVSHL,
	OP_BVLSHR,
	OP_BVASHR,
	OP_BVSHL1,
	OP_BVSHR1,
	OP_EQ,
	OP_NEQ,
	OP_AND,
	OP_OR,
	OP_XOR,
	OP_BVNOT,
	OP_BVNEG,
	OP_BVXOR,
	OP_BVADD,
	OP_BVAND,
	OP_BVOR,
	OP_BVMUL,
	OP_BVMUL_NO_OVERFLOW,
	OP_BVSUB,
	OP_BVUGE,
	OP_BVUGT,
	OP_BVULE,
	OP_BVULT,
	OP_BVSGE,
	OP_BVSGT,
	OP_BVSLE,
	OP_BVSLT,
	OP_BVSUBGE,
	OP_BVUDIV,
	OP_BVUREM,
	OP_ITE
};

// idea: make zero_extend, repeat, extract as functions!
// but I can't...
enum EXPR_TYPE
{
	EXPR_ID,
	EXPR_UNARY,
	EXPR_BINARY,
	EXPR_TERNARY,
	EXPR_CONST,
	EXPR_ZERO_EXTEND, // op1 and const_val are used!
	EXPR_REPEAT, // op1 and const_val are used!
	EXPR_EXTRACT // op1 and const_val and const_width are used!
};

struct expr
{
	enum EXPR_TYPE type; // rename to node_type?

	// in case of EXPR_ID
	char* id;

	// in case of EXPR_UNARY or EXPR_BINARY
	enum OP op;
	struct expr* op1;
	// in case of EXPR_BINARY
	struct expr* op2;
	// in case of EXPR_TERNARY (OP_ITE):
	struct expr* op3;

	// in case of EXPR_CONST
	//uint64_t const_val;
	uint32_t const_val;
	int const_width; // in bits

	// in case of chained expressions:
	struct expr *next;
};

struct expr* create_unary_expr(enum OP t, struct expr* op);
struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2);
struct expr* create_ternary_expr(enum OP t, struct expr* op1, struct expr* op2, struct expr* op3);
struct expr* create_vararg_expr(enum OP t, struct expr* args);
struct expr* create_distinct_expr(struct expr* args);
struct expr* create_const_expr(uint32_t c, int w);
struct expr* create_zero_extend_expr(int bits, struct expr* e);
struct expr* create_repeat_expr(int times, struct expr* e);
struct expr* create_extract_expr(unsigned end, unsigned start, struct expr* e);
struct expr* create_ITE(struct expr* sel, struct expr* t, struct expr* f);

struct SMT_var* create_variable(struct ctx* ctx, std::string name, enum TY type, int width, int internal);
struct ctx* init();
void create_assert (struct ctx* ctx, struct expr* e);
void create_min_max (struct ctx* ctx, struct expr* e, bool min_max);
void check_sat(struct ctx* ctx);
void get_model(struct ctx* ctx);
void get_all_models(struct ctx* ctx, bool dump_variables);

