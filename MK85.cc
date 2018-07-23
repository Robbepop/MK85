#include <iterator>
#include <string>
#include <list>
#include <algorithm>
#include <iostream>
#include <sstream>

#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>

#include "API.h"
#include "MK85.hh"
#include "utils.hh"

extern "C"
{
#include "picosat/picosat.h"
}

// from smt2.y:
extern int yylineno;

// TODO add command-line switch
int verbose;

// fwd decl:
struct SMT_var* find_variable(struct ctx* ctx, std::string id);
struct SMT_var* gen(struct ctx* ctx, struct expr* e);
struct SMT_var* gen_AND(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2);
struct SMT_var* gen_EQ(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2);
struct SMT_var* gen_ITE(struct ctx* ctx, struct SMT_var* sel, struct SMT_var* t, struct SMT_var* f);
struct SMT_var* gen_OR(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2);
struct SMT_var* gen_extract(struct ctx* ctx, struct SMT_var *v, unsigned begin, unsigned width);
struct SMT_var* gen_shift_left(struct ctx* ctx, struct SMT_var* X, unsigned int cnt);
struct SMT_var* gen_shift_right(struct ctx* ctx, struct SMT_var* X, unsigned int cnt, int SAT_var_new);
struct SMT_var* gen_zero_extend(struct ctx* ctx, struct SMT_var *in, int zeroes_to_add);
struct SMT_var* gen_repeat(struct ctx* ctx, struct SMT_var *in, int times);
void add_Tseitin_AND(struct ctx* ctx, int a, int b, int out);
void add_Tseitin_EQ(struct ctx* ctx, int v1, int v2);
void add_Tseitin_OR (struct ctx* ctx, int a, int b, int out);
void add_Tseitin_OR_list(struct ctx* ctx, int var, int width, int var_out);
void print_expr(struct expr* e);
const char* op_name(enum OP op);
struct SMT_var* gen_BVADD(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2);
void add_Tseitin_ITE_BV (struct ctx* ctx, int s, int t, int f, int x, int width);
void assure_TY_BOOL(const char* func, struct SMT_var* v);
void assure_TY_BITVEC(const char* func, struct SMT_var* v);
void assure_eq_widths(const char *name, struct SMT_var* v1, struct SMT_var* v2);
void fix_BV_to_zero (struct ctx* ctx, int v, int width);

void set_verbose(int level)
{
	verbose=level;
};

struct expr* create_id(struct ctx* ctx, char* id)
{
	if (verbose>=2)
	{
		printf ("%s(%s)\n", __FUNCTION__, id);
	};
	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_ID;

	struct SMT_var* v=find_variable(ctx, std::string(id));
	if(v==NULL)
		die ("line %d: variable %s hasn't been declared\n", yylineno, id);
	rt->type=v->type;
	rt->width=v->width;

	rt->id=id;
	rt->next=NULL;
	return rt;
};

struct expr* create_unary_expr(enum OP t, struct expr* op)
{
	if (verbose>=2)
	{
		printf ("%s()\n", __FUNCTION__);
		printf ("op=");
		print_expr(op);
		printf ("\n");
	};
	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->node_type=EXPR_UNARY;
	rt->type=op->type;
	rt->width=op->width;
	rt->op=t;
	rt->op1=op;
	return rt;
};

struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2)
{
	if (verbose>=2)
	{
		printf ("%s()\n", __FUNCTION__);
		printf ("t=%s\n", op_name(t));
		printf ("op1=");
		print_expr(op1);
		printf ("\n");
		printf ("op2=");
		print_expr(op2);
		printf ("\n");
	};

	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->node_type=EXPR_BINARY;
	if (t==OP_EQ || t==OP_NEQ || t==OP_BVUGE || t==OP_BVUGT || t==OP_BVULE || t==OP_BVULT)
	{
		rt->type=TY_BOOL;
		rt->width=1;
	}
	else
	{
		assert (op1->type==op2->type);
		assert (op1->width==op2->width);
		rt->type=op1->type;
		rt->width=op1->width;
	};

	if (verbose>=2)
	{
		printf ("%s(), rt->type=%d rt->width=%d\n", __FUNCTION__, rt->type, rt->width);
	};
	rt->op=t;
	rt->op1=op1;
	rt->op2=op2;
	return rt;
};

struct expr* create_ternary_expr(enum OP t, struct expr* op1, struct expr* op2, struct expr* op3)
{
	if (verbose>=2)
	{
		printf ("%s()\n", __FUNCTION__);
		printf ("op1=");
		print_expr(op1);
		printf ("\n");
		printf ("op2=");
		print_expr(op2);
		printf ("\n");
		printf ("op3=");
		print_expr(op3);
		printf ("\n");
	};

	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_TERNARY;
	//print_expr(op1); printf ("\n");
	//printf ("%d\n", op1->width==1);
	assert (op1->width==1);
	assert (op2->type==op3->type);
	assert (op2->width==op3->width);
	rt->type=op2->type;
	rt->width=op2->width;
	rt->op=t;
	rt->op1=op1;
	rt->op2=op2;
	rt->op3=op3;
	return rt;
};

// FIXME use STL here!
struct expr* create_vararg_expr(enum OP t, struct expr* args)
{
	if (verbose>=2)
	{
		printf ("%s(). input=\n", __FUNCTION__);
		for (struct expr* e=args; e; e=e->next)
		{
			print_expr(e);
			printf ("\n");
		};
	};

	// this provides left associativity.

	// be sure at least two expr in chain:
	if (args->next==NULL)
		die("line %d: '%s' requires 2 or more arguments!\n", yylineno, op_name(t));

	if (args->next->next==NULL)
		// only two expr in chain:
		return create_bin_expr(t, args->next, args);
	else
		// >2 expr in chain:
		return create_bin_expr(t, create_vararg_expr(t, args->next), args);
};

struct expr* create_distinct_expr(struct expr* args)
{
	// for 3 args:
	// and (a!=b, a!=c, b!=c)

	// FIXME use STL here!

	// be sure at least two expr in chain:
	if (args->next==NULL)
		die("line %d: 'distinct' requires at least 2 arguments!\n", yylineno);
	
	if (args->next->next==NULL)
		// only two expr in chain:
		return create_bin_expr (OP_NEQ, args->next, args);
	else
	{
		// >2 expr in chain:

		struct expr* e1=args;
		struct expr* big_AND_expr=NULL;
		for (struct expr* e2=args->next; e2; e2=e2->next)
		{
			struct expr* t=create_bin_expr (OP_NEQ, e1, e2);
			t->next=big_AND_expr;
			big_AND_expr=t;
		};
		// at this moment, big_AND_expr is chained expression of expr we will pass inside AND(...)
		struct expr *t=create_distinct_expr(args->next);
		t->next=big_AND_expr;
/*
		printf ("%s(). what we passing inside AND(...):\n", __FUNCTION__);
		print_expr(t);
		printf ("\n");
*/
		return create_vararg_expr(OP_AND, t);
	};
}

struct expr* create_const_expr(enum TY t, uint32_t c, int w)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, c, w);
	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_CONST;
	rt->const_val=c;
	rt->type=t;
	rt->width=w;
	return rt;
};

struct expr* create_zero_extend_expr(int bits, struct expr* e)
{
	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_ZERO_EXTEND;
	rt->const_val=bits;
	rt->op1=e;
	rt->type=TY_BITVEC;
	rt->width=e->width + bits; // unchecked
	return rt;
};

struct expr* create_repeat_expr(int times, struct expr* e)
{
	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_REPEAT;
	rt->const_val=times;
	rt->op1=e;
	rt->type=TY_BITVEC;
	rt->width=times * e->width; // unchecked
	return rt;
};

// get [start, end) bits
struct expr* create_extract_expr(unsigned end, unsigned start, struct expr* e)
{
	if (start>end)
		die ("line %d: start must be >=end, but you have start=%d, end=%d\n", yylineno, start, end);

	unsigned w=end-start+1;

	struct expr* rt=(struct expr*)xmalloc(sizeof(struct expr));
	rt->node_type=EXPR_EXTRACT;
	rt->const_val=start;
	rt->type=TY_BITVEC;
	rt->width=w;
	rt->op1=e;
	return rt;
};

const char* op_name(enum OP op)
{
	switch (op)
	{
		case OP_NOT:	return "not";
		case OP_EQ:	return "=";
		case OP_NEQ:	return "!="; // supported in SMT-LIB 2.x? not sure.
		case OP_OR:	return "or";
		case OP_XOR:	return "xor";
		case OP_AND:	return "and";

		case OP_BVNOT:	return "bvnot";
		case OP_BVNEG:	return "bvneg";
		case OP_BVOR:	return "bvor";
		case OP_BVXOR:	return "bvxor";
		case OP_BVADD:	return "bvadd";
		case OP_BVAND:	return "bvand";
		case OP_BVSUB:	return "bvsub";
		case OP_BVUGE:	return "bvuge";
		case OP_BVULE:	return "bvule";
		case OP_BVUGT:	return "bvugt";
		case OP_BVULT:	return "bvult";
		case OP_BVSGE:	return "bvsge";
		case OP_BVSLE:	return "bvsle";
		case OP_BVSGT:	return "bvsgt";
		case OP_BVSLT:	return "bvslt";
		case OP_BVSHL:	return "bvshl";
		case OP_BVLSHR:	return "bvlshr";
		case OP_BVASHR:	return "bvashr";
		case OP_BVMUL:	return "bvmul";
		case OP_BVMUL_NO_OVERFLOW:	return "bvmul_no_overflow";
		case OP_BVUDIV:	return "bvudiv";
		case OP_ITE:	return "ite";
		default:
			assert(0);
	};
};

// FIXME this meanness
void print_expr(struct expr* e)
{
	assert(e);

	switch (e->node_type)
	{
		case EXPR_ID:
			printf ("%s", e->id);
			return;

		case EXPR_CONST:
			printf ("%d (%d bits)", e->const_val, e->width);
			return;

		case EXPR_ZERO_EXTEND:
			printf ("(ZEXT by %d bits: ", e->const_val);
			print_expr(e->op1);
			printf (")");
			return;
		case EXPR_REPEAT:
			printf ("(repeat %d times: ", e->const_val);
			print_expr(e->op1);
			printf (")");
			return;
		case EXPR_EXTRACT:
			printf ("(extract, start=%d width=%d bits: ", e->const_val, e->width);
			print_expr(e->op1);
			printf (")");
			return;
		case EXPR_UNARY:
			printf ("(%s ", op_name(e->op));
			print_expr(e->op1);
			printf (")");
			return;
		case EXPR_BINARY:
			printf ("(%s ", op_name(e->op));
			print_expr(e->op1);
			printf (" ");
			print_expr(e->op2);
			printf (")");
			return;
		case EXPR_TERNARY:
			printf ("(%s ", op_name(e->op));
			print_expr(e->op1);
			printf (" ");
			print_expr(e->op2);
			printf (" ");
			print_expr(e->op3);
			printf (")");
			return;
		default:
			assert (0);
	}
};

// FIXME:
//static char expr_to_string_buf[102400]; // YES

// FIXME this meanness
std::string cpp_expr_to_string(struct expr* e)
{
	assert(e);
	std::string rt;
	char tbuf[128];

	switch (e->node_type)
	{
		case EXPR_ID:
			return std::string(e->id);

		case EXPR_CONST:
			sprintf (tbuf, "%d (%d bits)", e->const_val, e->width);
			return std::string(tbuf);

		case EXPR_ZERO_EXTEND:
			sprintf (tbuf, "(ZEXT by %d bits: ", e->const_val);
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+")";
			return rt;
		case EXPR_REPEAT:
			sprintf (tbuf, "(repeat %d times: ", e->const_val);
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+")";
			return rt;
		case EXPR_EXTRACT:
			sprintf (tbuf, "(extract, start=%d width=%d bits: ", e->const_val, e->width);
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+")";
			return rt;
		case EXPR_UNARY:
			sprintf (tbuf, "(%s ", op_name(e->op));
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+")";
			return rt;
		case EXPR_BINARY:
			sprintf (tbuf, "(%s ", op_name(e->op));
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+" ";
			rt=rt+expr_to_string(e->op2);
			rt=rt+")";
			return rt;

		case EXPR_TERNARY:
			sprintf (tbuf, "(%s ", op_name(e->op));
			rt=rt+std::string(tbuf);
			rt=rt+expr_to_string(e->op1);
			rt=rt+" ";
			rt=rt+expr_to_string(e->op2);
			rt=rt+" ";
			rt=rt+expr_to_string(e->op3);
			rt=rt+")";
			return rt;
		default:
			assert (0);
	}
};

// FIXME: how/when buffer should be be freed?
char * expr_to_string(struct expr* e)
{
	if (verbose)
		printf ("%s() begin\n", __FUNCTION__);

	char* rt=(char*)malloc(cpp_expr_to_string(e).size()+1);
	//strcpy (expr_to_string_buf, cpp_expr_to_string(e).c_str());
	strcpy (rt, cpp_expr_to_string(e).c_str());

	//return expr_to_string_buf;
	return rt;
};

const char* false_true_s[2]={"false", "true"};

void dump_all_variables(struct ctx* ctx, bool dump_internal)
{
	printf ("(model\n");
	for (auto i : ctx->vars)
	{
		struct SMT_var* v=i.second;

		if (v->internal && dump_internal==false)
			continue; // skip internal variables

		if (v->type==TY_BOOL)
		{
			assert (v->val<=1);
			if (dump_internal==false)
				printf ("\t(define-fun %s () Bool %s)\n", v->id.c_str(), false_true_s[v->val]);
			else
				printf ("\t(define-fun %s () Bool %s) ; SAT_var=%d\n", v->id.c_str(), false_true_s[v->val], v->SAT_var);
		}
		else if (v->type==TY_BITVEC)
		{
			if (dump_internal==false)
  				printf ("\t(define-fun %s () (_ BitVec %d) (_ bv%u %d)) ; 0x%x\n",
					v->id.c_str(), v->width, v->val, v->width, v->val);
			else
  				printf ("\t(define-fun %s () (_ BitVec %d) (_ bv%u %d)) ; 0x%x SAT_var=%d\n",
					v->id.c_str(), v->width, v->val, v->width, v->val, v->SAT_var);
		}
		else
		{
			assert(0);
		};
	}
	printf (")\n");

};

struct SMT_var* find_variable(struct ctx* ctx, std::string id)
{
	auto t=ctx->vars.find(id);
	if (t!=ctx->vars.end())
		return t->second;

	return NULL;
};

uint32_t get_variable_val(struct ctx* ctx, char* id)
{
	struct SMT_var* v=find_variable(ctx, std::string(id));
	if (v==NULL)
		die ("%s() can't find variable %s\n", __FUNCTION__, id);
	return v->val;
};

struct SMT_var* declare_variable(struct ctx* ctx, const char* name, enum TY type, int width, int internal)
{
	if (verbose && internal==0)
	{
		printf ("%s(name=%s, type=%d, width=%d, internal=%d)\n", __FUNCTION__, name, type, width, internal);
	};

	if (type==TY_BOOL)
		assert(width==1);

	if (find_variable(ctx, std::string(name))!=NULL)
		die ("Fatal error: variable %s is already defined\n", name);

	struct SMT_var *v=new(struct SMT_var);
	v->type=type;
	v->id=std::string(name);
	if (type==TY_BOOL)
	{
		v->SAT_var=ctx->SAT_next_var_no;
		v->width=1;
		ctx->SAT_next_var_no++;
	}
	else if (type==TY_BITVEC)
	{
		v->SAT_var=ctx->SAT_next_var_no;
		v->width=width;
		ctx->SAT_next_var_no+=width;
	}
	else
		assert(0);
	//printf ("%s() %s var_no=%d\n", __FUNCTION__, name, v->var_no);
	v->internal=internal;
	ctx->vars[v->id]=v;
	return v;
}

struct SMT_var* create_internal_variable(struct ctx* ctx, const char* prefix, enum TY type, int width)
{
	char tmp[128];
	snprintf (tmp, sizeof(tmp), "%s!%d", prefix, ctx->next_internal_var);
	ctx->next_internal_var++;
	return declare_variable(ctx, tmp, type, width, 1);
};

void add_soft_clause1(struct ctx* ctx, uint32_t weight, int v1)
{
	ctx->clauses_t++;

	class clause c;
	c.type=SOFT_CLAUSE;
	c.weight=weight;
	c.li.push_back(v1);
	ctx->clauses.push_back(c);

	ctx->max_weight=std::max(ctx->max_weight, weight);
	ctx->maxsat=true;
};

void add_clause1(struct ctx* ctx, int v1)
{
	ctx->clauses_t++;
	class clause c;
	c.type=HARD_CLASUE;
	c.li.push_back(v1);
	ctx->clauses.push_back(c);
	//ctx->clauses.push_front(c);
};

void add_clause2(struct ctx* ctx, int v1, int v2)
{
	ctx->clauses_t++;
	class clause c;
	c.type=HARD_CLASUE;
	c.li.push_back(v1);
	c.li.push_back(v2);
	ctx->clauses.push_back(c);
	//ctx->clauses.push_front(c);
};

void add_clause3(struct ctx* ctx, int v1, int v2, int v3)
{
	ctx->clauses_t++;
	class clause c;
	c.type=HARD_CLASUE;
	c.li.push_back(v1);
	c.li.push_back(v2);
	c.li.push_back(v3);
	ctx->clauses.push_back(c);
	//ctx->clauses.push_front(c);
};

void add_clause4(struct ctx* ctx, int v1, int v2, int v3, int v4)
{
	ctx->clauses_t++;
	class clause c;
	c.type=HARD_CLASUE;
	c.li.push_back(v1);
	c.li.push_back(v2);
	c.li.push_back(v3);
	c.li.push_back(v4);
	ctx->clauses.push_back(c);
	//ctx->clauses.push_front(c);
};

void add_comment(struct ctx* ctx, const char* fmt, ...)
{
	if (ctx->write_CNF_file==false)
		return;

	va_list va;

	va_start (va, fmt);
	size_t buflen=vsnprintf (NULL, 0, fmt, va)+2+1;
	va_end(va);

	char* buf=(char*)xmalloc(buflen+2/*+current_indent*/);
	buf[0]='c';
	buf[1]=' ';

	// add indentation:
	//for (int i=0; i<current_indent; i++)
	//	buf[2+i]=' ';

	va_start (va, fmt);
	size_t written=vsnprintf (buf+2/*+current_indent*/, buflen, fmt, va);
	va_end(va);

	assert (written<buflen);

	class clause c;
	c.type=COMMENT;
	c.s=buf;
	ctx->clauses.push_back(c);
	//ctx->clauses.push_front(c);
};

struct SMT_var* gen_const(struct ctx* ctx, uint32_t val, int width)
{
	if (verbose)
		printf ("%s(%d, %d) begin\n", __FUNCTION__, val, width);
	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BITVEC, width);
	add_comment(ctx, "gen_const(val=%d, width=%d). SAT_var=[%d..%d]", val, width, rt->SAT_var, rt->SAT_var+width-1);
	for (int i=0; i<width; i++)
	{
		if ((val>>i)&1)
		{
			// add "always true" for this bit
			add_clause1 (ctx, rt->SAT_var+i);
		}
		else
		{
			// add "always false" for this bit
			add_clause1 (ctx, -(rt->SAT_var+i));
		}
	};
	if (verbose)
		printf ("%s(%d, %d) end\n", __FUNCTION__, val, width);
	return rt;
}

void add_Tseitin_NOT(struct ctx* ctx, int v1, int v2)
{
	add_clause2 (ctx, -v1, -v2);
	add_clause2 (ctx, v1, v2);
}

struct SMT_var* gen_NOT(struct ctx* ctx, struct SMT_var* v)
{
	assure_TY_BOOL("not", v);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BOOL, 1);
	add_comment (ctx, "gen_NOT id (SMT) %s, (SAT) var=%d, out (SMT) id=%s out (SAT) var=%d", v->id.c_str(), v->SAT_var, rt->id.c_str(), rt->SAT_var);
	add_Tseitin_NOT (ctx, rt->SAT_var, v->SAT_var);
	return rt;
};

struct SMT_var* gen_BVNOT(struct ctx* ctx, struct SMT_var* v)
{
	assure_TY_BITVEC("bvnot", v);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BITVEC, v->width);
	add_comment (ctx, "gen_BVNOT");
	for (int i=0; i<v->width; i++)
		add_Tseitin_NOT (ctx, rt->SAT_var+i, v->SAT_var+i);
	return rt;
};

// ... or die
void assure_TY_BITVEC(const char* func, struct SMT_var* v)
{
	if (v->type==TY_BITVEC)
		return;
	printf ("Error: sort mismatch: '%s' takes bitvec expression, but %s is not\n", func, v->id.c_str());
	printf ("which is: "); print_expr (v->e); printf ("\n");
	exit(0);
}

// ... or die
void assure_TY_BOOL(const char* func, struct SMT_var* v)
{
	if (v->type==TY_BOOL)
		return;
	printf ("Error: sort mismatch: '%s' takes boolean expression, but %s is not\n", func, v->id.c_str());
	printf ("which is: "); print_expr (v->e); printf ("\n");
	exit(0);
}

struct SMT_var* gen_BVNEG(struct ctx* ctx, struct SMT_var* v)
{
	assure_TY_BITVEC("bvneg", v);

	add_comment (ctx, "gen_BVNEG");
	return gen_BVADD(ctx, gen_BVNOT(ctx, v), gen_const(ctx, 1, v->width));
};

void add_Tseitin_XOR(struct ctx* ctx, int v1, int v2, int v3)
{
	add_comment (ctx, "%s %d=%d^%d", __FUNCTION__, v3, v1, v2);
	add_clause3 (ctx, -v1, -v2, -v3);
	add_clause3 (ctx, v1, v2, -v3);
	add_clause3 (ctx, v1, -v2, v3);
	add_clause3 (ctx, -v1, v2, v3);
};

void add_Tseitin_OR2(struct ctx* ctx, int v1, int v2, int var_out)
{
	add_comment (ctx, "%s %d=%d|%d", __FUNCTION__, var_out, v1, v2);
	add_clause3(ctx, v1, v2, -var_out);
	add_clause2(ctx, -v1, var_out);
	add_clause2(ctx, -v2, var_out);
};

void add_FA(struct ctx* ctx, int a, int b, int cin, int s, int cout)
{
	add_comment(ctx, "%s inputs=%d, %d, cin=%d, s=%d, cout=%d", __FUNCTION__, a, b, cin, s, cout);
#if 1
	// full-adder, as found by Mathematica using truth table:
	// TODO which is faster?
        add_clause4(ctx, -a, -b, -cin, s);
        add_clause3(ctx, -a, -b, cout);
        add_clause3(ctx, -a, -cin, cout);
        add_clause3(ctx, -a, cout, s);
        add_clause4(ctx, a, b, cin, -s);
        add_clause3(ctx, a, b, -cout);
        add_clause3(ctx, a, cin, -cout);
        add_clause3(ctx, a, -cout, -s);
        add_clause3(ctx, -b, -cin, cout);
        add_clause3(ctx, -b, cout, s);
        add_clause3(ctx, b, cin, -cout);
        add_clause3(ctx, b, -cout, -s);
        add_clause3(ctx, -cin, cout, s);
        add_clause3(ctx, cin, -cout, -s);
#endif
#if 0
	// do the same, using gates and Tseitin transformations.
	// allocate 3 "joint" variables:
	int XOR1_out=SAT_next_var_no++;
	int AND1_out=SAT_next_var_no++;
	int AND2_out=SAT_next_var_no++;
	// add gates and connect them.
	// order doesn't matter, BTW:
	add_Tseitin_XOR(a, b, XOR1_out);
	add_Tseitin_XOR(XOR1_out, cin, s);
	add_Tseitin_AND(XOR1_out, cin, AND1_out);
	add_Tseitin_AND(a, b, AND2_out);
	add_Tseitin_OR2(AND1_out, AND2_out, cout);
#endif
};

void gen_adder(struct ctx* ctx, struct SMT_var* a, struct SMT_var* b, struct SMT_var *carry_in, // inputs
	struct SMT_var** sum, struct SMT_var** carry_out) // outputs
{
	assure_TY_BITVEC("adder", a);
	assure_TY_BITVEC("adder", b);
	assure_eq_widths("adder", a, b);
	assure_TY_BOOL("adder", carry_in);

	*sum=create_internal_variable(ctx, "adder_sum", TY_BITVEC, a->width);
	add_comment (ctx, "%s", __FUNCTION__);

	int carry=carry_in->SAT_var;
	int carry_out_tmp=0; // make compiler happy

	// the first full-adder could be half-adder, but we make things simple here
	for (int i=0; i<a->width; i++)
	{
		carry_out_tmp=ctx->SAT_next_var_no++;
		add_FA(ctx, a->SAT_var+i, b->SAT_var+i, carry, (*sum)->SAT_var+i, carry_out_tmp);
		// newly created carry_out is a carry_in for the next full-adder:
		carry=carry_out_tmp;
	};

	*carry_out=create_internal_variable(ctx, "adder_carry", TY_BOOL, 1);
	add_Tseitin_EQ(ctx, carry_out_tmp, (*carry_out)->SAT_var);
};

struct SMT_var* gen_BVADD(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvadd", v1);
	assure_TY_BITVEC("bvadd", v2);
	assure_eq_widths("bvadd", v1, v2);

	struct SMT_var *sum;
	struct SMT_var *carry_out;
	gen_adder(ctx, v1, v2, ctx->var_always_false, &sum, &carry_out);
	return sum;
};

// TODO use Tseitin + gates?
// full-subtractor, as found by Mathematica using truth table:
void add_FS(struct ctx* ctx, int x, int y, int bin, int d, int bout)
{
	add_comment(ctx, "add_FS");
	add_clause3(ctx, -bin, bout, -d);
	add_clause3(ctx, -bin, bout, -y);
	add_clause4(ctx, -bin, -d, -x, y);
	add_clause4(ctx, -bin, -d, x, -y);
	add_clause4(ctx, -bin, d, -x, -y);
	add_clause4(ctx, -bin, d, x, y);
	add_clause3(ctx, bin, -bout, d);
	add_clause3(ctx, bin, -bout, y);
	add_clause4(ctx, bin, -d, -x, -y);
	add_clause4(ctx, bin, -d, x, y);
	add_clause4(ctx, bin, d, -x, y);
	add_clause4(ctx, bin, d, x, -y);
	add_clause3(ctx, -bout, d, y);
	add_clause3(ctx, bout, -d, -y);
};

void gen_subtractor(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2, 
	struct SMT_var** rt, struct SMT_var** borrow_out)
{
	assure_TY_BITVEC("subtractor", v1);
	assure_TY_BITVEC("subtractor", v2);
	assure_eq_widths("subtractor", v1, v2);

	*rt=create_internal_variable(ctx, "SUB_result", TY_BITVEC, v1->width);

	add_comment (ctx, __FUNCTION__);

	int borrow=ctx->var_always_false->SAT_var;

	// the first full-subtractor could be half-subtractor, but we make things simple here
	for (int i=0; i<v1->width; i++)
	{
		*borrow_out=create_internal_variable(ctx, "internal", TY_BOOL, 1);
		add_FS(ctx, v1->SAT_var+i, v2->SAT_var+i, borrow, (*rt)->SAT_var+i, (*borrow_out)->SAT_var);
		// newly created borrow_out is a borrow_in for the next full-subtractor:
		borrow=(*borrow_out)->SAT_var;
	};
};

struct SMT_var* gen_BVSUB(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvsub", v1);
	assure_TY_BITVEC("bvsub", v2);
	assure_eq_widths("bvsub", v1, v2);

	struct SMT_var* rt=NULL;
	struct SMT_var* borrow_out=NULL;

	gen_subtractor(ctx, v1, v2, &rt, &borrow_out);

	return rt;
};

struct SMT_var* gen_BVSUB_borrow(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC(__FUNCTION__, v1);
	assure_TY_BITVEC(__FUNCTION__, v2);
	assure_eq_widths(__FUNCTION__, v1, v2);

	struct SMT_var* rt=NULL;
	struct SMT_var* borrow_out=NULL;

	gen_subtractor(ctx, v1, v2, &rt, &borrow_out);

	return borrow_out;
};

struct SMT_var* gen_BVULT(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvult", v1);
	assure_TY_BITVEC("bvult", v2);
	assure_eq_widths("bvult", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_BVSUB_borrow(ctx, v1, v2);
};

struct SMT_var* gen_BVULE(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvule", v1);
	assure_TY_BITVEC("bvule", v2);
	assure_eq_widths("bvule", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_OR(ctx, gen_BVULT(ctx, v1, v2), gen_EQ(ctx, v1, v2));
};

struct SMT_var* gen_BVUGT(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvugt", v1);
	assure_TY_BITVEC("bvugt", v2);
	assure_eq_widths("bvugt", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_BVSUB_borrow(ctx, v2, v1);
};

struct SMT_var* gen_BVUGE(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvuge", v1);
	assure_TY_BITVEC("bvuge", v2);
	assure_eq_widths("bvuge", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_OR(ctx, gen_BVUGT(ctx, v1, v2), gen_EQ(ctx, v1, v2));
};

/*
see also: http://smtlib.cs.uiowa.edu

   (bvslt s t) abbreviates:
      (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
               (= ((_ extract |m-1| |m-1|) t) #b0))
          (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
               (bvult s t)))
*/
struct SMT_var* gen_BVSLT(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvslt", v1);
	assure_TY_BITVEC("bvslt", v2);
	assure_eq_widths("bvslt", v1, v2);
	add_comment (ctx, __FUNCTION__);

	// get signs of operands:
	struct SMT_var* v1_MSB=gen_extract(ctx, v1, v1->width-1, 1);
	struct SMT_var* v2_MSB=gen_extract(ctx, v2, v2->width-1, 1);

	struct SMT_var* MSBs_are_00=gen_AND(ctx, gen_EQ(ctx, v1_MSB, ctx->var_always_false), gen_EQ(ctx, v2_MSB, ctx->var_always_false));
	struct SMT_var* MSBs_are_01=gen_AND(ctx, gen_EQ(ctx, v1_MSB, ctx->var_always_false), gen_EQ(ctx, v2_MSB, ctx->var_always_true));
	struct SMT_var* MSBs_are_10=gen_AND(ctx, gen_EQ(ctx, v1_MSB, ctx->var_always_true), gen_EQ(ctx, v2_MSB, ctx->var_always_false));
	struct SMT_var* MSBs_are_11=gen_AND(ctx, gen_EQ(ctx, v1_MSB, ctx->var_always_true), gen_EQ(ctx, v2_MSB, ctx->var_always_true));

	struct SMT_var* unsigned_comparison=gen_BVULT(ctx, v1, v2);

	// this is like switch():
	return 
		gen_ITE(ctx, MSBs_are_00, unsigned_comparison,
		gen_ITE(ctx, MSBs_are_01, ctx->var_always_false,
		gen_ITE(ctx, MSBs_are_10, ctx->var_always_true,
		gen_ITE(ctx, MSBs_are_11, unsigned_comparison,
			ctx->var_always_false)))); // default, but we can't get here
};

struct SMT_var* gen_BVSLE(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvsle", v1);
	assure_TY_BITVEC("bvsle", v2);
	assure_eq_widths("bvsle", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_OR(ctx, gen_BVSLT(ctx, v1, v2), gen_EQ(ctx, v1, v2));
};

struct SMT_var* gen_BVSGT(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvsgt", v1);
	assure_TY_BITVEC("bvsgt", v2);
	assure_eq_widths("bvsgt", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_BVSLT(ctx, v2, v1);
};

struct SMT_var* gen_BVSGE(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvsge", v1);
	assure_TY_BITVEC("bvsge", v2);
	assure_eq_widths("bvsge", v1, v2);
	add_comment (ctx, __FUNCTION__);

	return gen_OR(ctx, gen_BVSGT(ctx, v1, v2), gen_EQ(ctx, v1, v2));
};

// it's like SUBGE in ARM CPU in ARM mode
// rationale: used in divisor!
void gen_BVSUBGE(struct ctx* ctx, struct SMT_var* enable, struct SMT_var* v1, struct SMT_var* v2,
	struct SMT_var** output, struct SMT_var** cond)
{
	assure_TY_BITVEC("bvsubge", v1);
	assure_TY_BITVEC("bvsubge", v2);
	assure_eq_widths("bvsubge", v1, v2);

	*cond=gen_BVUGE(ctx, v1, v2);
	struct SMT_var *diff=gen_BVSUB(ctx, v1, v2);

	*output=gen_ITE(ctx, enable, gen_ITE(ctx, *cond, diff, v1), v1);
};

void add_Tseitin_BV_is_zero (struct ctx* ctx, int SAT_var, int width, int SAT_var_out)
{
	// all bits in BV are zero?

	struct SMT_var *tmp=create_internal_variable(ctx, "tmp", TY_BOOL, 1); // FIXME ++
	add_Tseitin_OR_list(ctx, SAT_var, width, tmp->SAT_var);
	add_Tseitin_NOT(ctx, tmp->SAT_var, SAT_var_out);
};

void gen_divisor (struct ctx* ctx, struct SMT_var* divident, struct SMT_var* divisor, struct SMT_var** q, struct SMT_var** r)
{
	assure_TY_BITVEC("divident", divident);
	assure_TY_BITVEC("divisor", divisor);
	assure_eq_widths("divisor", divident, divisor);

	int w=divident->width;
	struct SMT_var* wide1=gen_zero_extend(ctx, divisor, w);
	struct SMT_var* wide2=gen_shift_left(ctx, wide1, w-1);

	*q=create_internal_variable(ctx, "quotient", TY_BITVEC, w);

	for (int i=0; i<w; i++)
	{
		struct SMT_var* enable=create_internal_variable(ctx, "enable", TY_BOOL, 1);
		// enable is 1 if high part of wide2 is cleared
		add_Tseitin_BV_is_zero (ctx, wide2->SAT_var+w, w, enable->SAT_var);

		struct SMT_var* cond;
		gen_BVSUBGE(ctx, enable, divident, gen_extract(ctx, wide2, 0, w), &divident, &cond);
		struct SMT_var* latch2;
		// output bit must be zero if enable==0 (IOW: if high part of wide2 is not zero)
		latch2=gen_ITE(ctx, enable, cond, ctx->var_always_false);
		add_Tseitin_EQ(ctx, latch2->SAT_var, (*q)->SAT_var+w-1-i);
		if (i+1==w)
			break;
		wide2=gen_shift_right(ctx, wide2, 1, ctx->var_always_false->SAT_var);
	};
	*r=divident;
};

struct SMT_var* gen_BVUDIV(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	struct SMT_var *q;
	struct SMT_var *r;

	gen_divisor (ctx, v1, v2, &q, &r);

	// remainderless division?!
	//int w=r->width;
	//fix_BV_to_zero (ctx, r->SAT_var, w);

	return q;
};

struct SMT_var* gen_BVUREM(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	struct SMT_var *q;
	struct SMT_var *r;

	gen_divisor (ctx, v1, v2, &q, &r);

	return r;
};

struct SMT_var* gen_XOR(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	if (v1->width!=1 || v2->width!=1)
		die ("line %d: sort mismatch, xor requires 1-bit bools or bitvecs, you supplied %d and %d\n", yylineno, v1->width, v2->width);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BOOL, 1);
	add_comment (ctx, "gen_XOR id1 (SMT) %s id2 (SMT) %s var1 (SAT) %d var2 (SAT) %d out (SMT) id %s out (SAT) var=%d",
		v1->id.c_str(), v2->id.c_str(), v1->SAT_var, v2->SAT_var, rt->id.c_str(), rt->SAT_var);
	add_Tseitin_XOR (ctx, v1->SAT_var, v2->SAT_var, rt->SAT_var);
	return rt;
};

struct SMT_var* gen_BVAND(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvand", v1);
	assure_TY_BITVEC("bvand", v2);
	assure_eq_widths("bvand", v1, v2);

	struct SMT_var* rt=create_internal_variable(ctx, "AND_result", TY_BITVEC, v1->width);
	add_comment (ctx, __FUNCTION__);
	for (int i=0; i<v1->width; i++)
		add_Tseitin_AND (ctx, v1->SAT_var+i, v2->SAT_var+i, rt->SAT_var+i); // FIXME use _BV
	return rt;
};

// ... or die
void assure_eq_widths(const char *name, struct SMT_var* v1, struct SMT_var* v2)
{
	if(v1->width==v2->width)
		return;

	printf ("line %d. %s can't work on bitvectors of different widths. you supplied %d and %d\n",
		yylineno, name, v1->width, v2->width);
	printf ("v1. id==%s, e=", v1->id.c_str()); print_expr(v1->e); printf ("\n");
	printf ("v2. id==%s, e=", v2->id.c_str()); print_expr(v2->e); printf ("\n");
	exit(0);

};

struct SMT_var* gen_BVOR(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvor", v1);
	assure_TY_BITVEC("bvor", v2);
	assure_eq_widths("bvor", v1, v2);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BITVEC, v1->width);
	add_comment (ctx, "gen_BVOR v1 (SAT) [%d...%d], v2 (SAT) [%d...%d]",
		v1->SAT_var, v1->SAT_var+v1->width-1,
		v2->SAT_var, v2->SAT_var+v2->width-1);
	for (int i=0; i<v1->width; i++)
		add_Tseitin_OR (ctx, v1->SAT_var+i, v2->SAT_var+i, rt->SAT_var+i); // FIXME use _BV
	return rt;
};

struct SMT_var* gen_BVXOR(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	assure_TY_BITVEC("bvxor", v1);
	assure_TY_BITVEC("bvxor", v2);
	assure_eq_widths("bvxor", v1, v2);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BITVEC, v1->width);
	add_comment (ctx, "gen_BVXOR v1 (SAT) [%d...%d], v2 (SAT) [%d...%d]",
		v1->SAT_var, v1->SAT_var+v1->width-1,
		v2->SAT_var, v2->SAT_var+v2->width-1);
	for (int i=0; i<v1->width; i++)
		add_Tseitin_XOR (ctx, v1->SAT_var+i, v2->SAT_var+i, rt->SAT_var+i); // FIXME use _BV
	return rt;
};

// as in Tseitin transformations.
// return=var OR var+1 OR ... OR var+width-1
void add_Tseitin_OR_list(struct ctx* ctx, int var, int width, int var_out)
{
	add_comment (ctx, "%s(var=%d, width=%d, var_out=%d)", __FUNCTION__, var, width, var_out);
	class clause c;
	c.type=HARD_CLASUE;
	for (int i=var; i<var+width; i++)
		c.li.push_back(i);
	c.li.push_back(-var_out);
	ctx->clauses.push_back(c);
	ctx->clauses_t++;

	for (int i=0; i<width; i++)
		add_clause2(ctx, -(var+i), var_out);
};

struct SMT_var* gen_OR_list(struct ctx* ctx, int var, int width)
{
	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BOOL, 1);
	add_comment (ctx, "%s(var=%d, width=%d), var out (SAT) %d", __FUNCTION__, var, width, rt->SAT_var);
	add_Tseitin_OR_list(ctx, var, width, rt->SAT_var);
	return rt;
};

struct SMT_var* gen_EQ(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	if (verbose>=2)
		printf ("%s() v1->SAT_var=%d v2->SAT_var=%d\n", __FUNCTION__, v1->SAT_var, v2->SAT_var);

	if (v1->width==1)
	{
		if(v2->width!=1)
		{
			printf ("%s() sort mismatch\n", __FUNCTION__);
			printf ("v1=%s type=%d width=%d\n", v1->id.c_str(), v1->type, v1->width);
			printf ("v2=%s type=%d width=%d\n", v2->id.c_str(), v2->type, v2->width);
			die("");
		};
		add_comment (ctx, "gen_EQ id1 (SMT) %s, id2 (SMT) %s, var1 (SAT) %d, var2 (SAT) %d", v1->id.c_str(), v2->id.c_str(), v1->SAT_var, v2->SAT_var);
		//current_indent++;
		struct SMT_var *v=gen_NOT(ctx, gen_XOR(ctx, v1, v2));
		//current_indent--;
		if (verbose>=2)
			printf ("%s() returns %s (Bool)\n", __FUNCTION__, v->id.c_str());
		return v;
	}
	else
	{
		assure_TY_BITVEC("=", v2);
		assure_eq_widths("=", v1, v2);

		add_comment (ctx, "gen_EQ for two bitvectors, v1 (SAT) [%d...%d], v2 (SAT) [%d...%d]", 
			v1->SAT_var, v1->SAT_var+v1->width-1,
			v2->SAT_var, v2->SAT_var+v2->width-1);
		struct SMT_var* t=gen_BVXOR(ctx, v1,v2);
		struct SMT_var* v=gen_NOT(ctx, gen_OR_list(ctx, t->SAT_var, t->width));
		if (verbose>=2)
			printf ("%s() returns %s (bitvec %d)\n", __FUNCTION__, v->id.c_str(), v->width);
		return v;
	};
};

struct SMT_var* gen_NEQ(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	return gen_NOT(ctx, gen_EQ(ctx, v1,v2));
};

void add_Tseitin_AND(struct ctx* ctx, int a, int b, int out)
{
	add_comment (ctx, "%s %d=%d&%d", __FUNCTION__, out, a, b);
	add_clause3 (ctx, -a, -b, out);
	add_clause2 (ctx, a, -out);
	add_clause2 (ctx, b, -out);
};

struct SMT_var* gen_AND(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BOOL, 1);
	add_comment (ctx, "gen_AND id1 (SMT) %s, id2 (SMT) %s, var1 (SAT) %d, var2 (SAT) %d, out id (SMT) %s, out var (SAT) %d", 
		v1->id.c_str(), v2->id.c_str(), v1->SAT_var, v2->SAT_var, rt->id.c_str(), rt->SAT_var);
	add_Tseitin_AND(ctx, v1->SAT_var, v2->SAT_var, rt->SAT_var);
	return rt;
};

void add_Tseitin_mult_by_bit(struct ctx* ctx, int width, int SAT_var_in, int SAT_var_out, int SAT_var_bit)
{
	for (int i=0; i<width; i++)
		add_Tseitin_AND(ctx, SAT_var_in+i, SAT_var_bit, SAT_var_out+i);
};
/*
struct SMT_var* gen_mult_by_bit(struct SMT_var *in, struct SMT_var* bit)
{
	assert (in->type==TY_BITVEC);
	assert (bit->type==TY_BOOL);

	struct SMT_var* rt=create_internal_variable("internal", TY_BITVEC, in->width);

	add_Tseitin_mult_by_bit(in->width, in->var_no, rt->var_no, bit->var_no);
	return rt;
};
*/
// v1=v2 always!
void add_Tseitin_EQ(struct ctx* ctx, int v1, int v2)
{
	add_clause2 (ctx, -v1, v2);
	add_clause2 (ctx, v1, -v2);
}

// FIXME rename _BV
void add_Tseitin_EQ_bitvecs(struct ctx* ctx, int width, int v1, int v2)
{
	for (int i=0; i<width; i++)
		add_Tseitin_EQ(ctx, v1+i, v2+i);
}

void add_Tseitin_bitvec_eq_to_bool(struct ctx* ctx, int width, int bv, int b)
{
	for (int i=0; i<width; i++)
		add_Tseitin_EQ(ctx, bv+i, b);
}

void fix_BV_to_zero (struct ctx* ctx, int v, int width)
{
	for (int i=0; i<width; i++)
		add_clause1(ctx, -(v+i));
};

struct SMT_var* gen_zero_extend(struct ctx* ctx, struct SMT_var *in, int zeroes_to_add)
{
	int final_width=in->width+zeroes_to_add;
	struct SMT_var* rt=create_internal_variable(ctx, "zero_extended", TY_BITVEC, final_width);

	add_Tseitin_EQ_bitvecs(ctx, in->width, in->SAT_var, rt->SAT_var);
	fix_BV_to_zero (ctx, rt->SAT_var + in->width, zeroes_to_add);

	return rt;
};

struct SMT_var* gen_repeat_from_SAT_var(struct ctx* ctx, int SAT_var, int width, int times)
{
	int final_width=width*times;
	struct SMT_var* rt=create_internal_variable(ctx, "repeat", TY_BITVEC, final_width);

	for (int i=0; i<times; i++)
		add_Tseitin_EQ_bitvecs(ctx, width, SAT_var, rt->SAT_var + width*i);

	return rt;
};

struct SMT_var* gen_repeat(struct ctx* ctx, struct SMT_var *in, int times)
{
	return gen_repeat_from_SAT_var(ctx, in->SAT_var, in->width, times);
};

// "cnt" is not a SMT variable!
struct SMT_var* gen_shift_left(struct ctx* ctx, struct SMT_var* X, unsigned int cnt)
{
	int w=X->width;

	struct SMT_var* rt=create_internal_variable(ctx, "shifted_left", TY_BITVEC, w);

	fix_BV_to_zero(ctx, rt->SAT_var, cnt);

	add_Tseitin_EQ_bitvecs(ctx, w-cnt, rt->SAT_var+cnt, X->SAT_var);

	return rt;
};

// cnt is not a SMT variable!
// SAT_var_new can be TRUE in case of bvashr, or it can just be connected to always_false
struct SMT_var* gen_shift_right(struct ctx* ctx, struct SMT_var* X, unsigned int cnt, int SAT_var_new)
{
	int w=X->width;

	struct SMT_var* rt=create_internal_variable(ctx, "shifted_right", TY_BITVEC, w);

	add_Tseitin_bitvec_eq_to_bool(ctx, cnt, rt->SAT_var+w-cnt, SAT_var_new);
	//fix_BV_to_zero(rt->SAT_var+w-cnt, cnt);

	add_Tseitin_EQ_bitvecs(ctx, w-cnt, rt->SAT_var, X->SAT_var+cnt);
	return rt;
};

// returns SAT_var
int MSB_of_SMT_var (struct SMT_var *v)
{
	return v->SAT_var + v->width-1;
};

// direction=false for shift left
// direction=true for shift right
// arith=true is for bvashr (only for shifting right)

// for 8-bit left shifter, this is:
// X=ITE(cnt&1, X<<1, X)
// X=ITE((cnt>>1)&1, X<<2, X)
// X=ITE((cnt>>2)&1, X<<4, X)
// i.e., if the bit is set in cnt, shift X by that ammount of bits, or do nothing otherwise

struct SMT_var* gen_shifter_real (struct ctx* ctx, struct SMT_var* X, struct SMT_var* cnt, bool direction, bool arith)
{
	int w=X->width;

	struct SMT_var* in=X;
	struct SMT_var* out;
	struct SMT_var* tmp;

	// bit vector must have width=2^x, i.e., 8, 16, 32, 64, etc
	// FIXME better func name:
	assert (popcount64c (w)==1);

	int bits_in_selector=mylog2(w);

	for (int i=0; i<bits_in_selector; i++)
	{
		if (direction==false)
			tmp=gen_shift_left(ctx, in, 1<<i);
		else
			tmp=gen_shift_right(ctx, in, 1<<i, arith ? MSB_of_SMT_var(X) : ctx->var_always_false->SAT_var);

		out=create_internal_variable(ctx, "tmp", TY_BITVEC, w);

		add_Tseitin_ITE_BV (ctx, cnt->SAT_var+i, tmp->SAT_var, in->SAT_var, out->SAT_var, w);

		in=out;
	};

	// if any bit is set in high part of "cnt" variable, result is 0
	// i.e., if a 8-bit bitvector is shifted by cnt>8, give a zero
	struct SMT_var *disable_shifter=create_internal_variable(ctx, "...", TY_BOOL, 1);
	add_Tseitin_OR_list(ctx, cnt->SAT_var+bits_in_selector, w-bits_in_selector, disable_shifter->SAT_var);

	// 0x80 >>s cnt, where cnt>8, must be 0xff! so fill result with MSB(input)
	struct SMT_var *default_val;
	if (arith==false)
		default_val=gen_const(ctx, 0, w);
	else
		default_val=gen_repeat_from_SAT_var(ctx, MSB_of_SMT_var(X), 1, w);

	return gen_ITE(ctx, disable_shifter, default_val, in);
};

struct SMT_var* gen_shifter (struct ctx* ctx, struct SMT_var* X, struct SMT_var* cnt, bool direction, bool arith)
{
	int w=X->width;

	// FIXME: better func name:
	if (popcount64c (w)!=1)
	{
		// X is not in 2^n form, so extend it
		// RATIONALE: input must be in $2^n$ form, so the shift count will be $n$
		//printf ("%s() width=%d\n", __FUNCTION__, w);
		int new_w=1<<(mylog2(w)+1);
		//printf ("%s() extending it to width=%d\n", __FUNCTION__, new_w);
		X=gen_zero_extend(ctx, X, new_w-w);
		cnt=gen_zero_extend(ctx, cnt, new_w-w);
	}

	struct SMT_var* rt=gen_shifter_real(ctx, X, cnt, direction, arith);

	if (popcount64c (w)!=1)
	{
		// X is not in 2^n form
		rt=gen_extract (ctx, rt, 0, w);
	};

	return rt;
};

struct SMT_var* gen_BVSHL (struct ctx* ctx, struct SMT_var* X, struct SMT_var* cnt)
{
	return gen_shifter (ctx, X, cnt, false, false);
};

struct SMT_var* gen_BVLSHR (struct ctx* ctx, struct SMT_var* X, struct SMT_var* cnt)
{
	return gen_shifter (ctx, X, cnt, true, false);
};

struct SMT_var* gen_BVASHR (struct ctx* ctx, struct SMT_var* X, struct SMT_var* cnt)
{
	return gen_shifter (ctx, X, cnt, true, true);
};

struct SMT_var* gen_extract(struct ctx* ctx, struct SMT_var *v, unsigned begin, unsigned width)
{
	struct SMT_var* rt=create_internal_variable(ctx, "extracted", TY_BITVEC, width);
	add_Tseitin_EQ_bitvecs(ctx, width, rt->SAT_var, v->SAT_var+begin);

	return rt;
};

// type:
// 0 - usual
// 1 - no overflow
struct SMT_var* gen_BVMUL(struct ctx* ctx, struct SMT_var* X, struct SMT_var* Y, int type)
{
	assure_TY_BITVEC("bvmul", X);
	assure_TY_BITVEC("bvmul", Y);
	assure_eq_widths("bvmul", X, Y);

	int w=X->width;
	int final_w=w*2;

	struct SMT_var* X_extended=gen_zero_extend(ctx, X, w);

	struct SMT_var* partial_products1[w]; // warning: GCC (?) extension
	struct SMT_var* partial_products2[w]; // warning: GCC (?) extension

	for (int i=0; i<w; i++)
	{
		partial_products1[i]=create_internal_variable(ctx, "partial_product1", TY_BITVEC, final_w);
		add_Tseitin_mult_by_bit(ctx, final_w, X_extended->SAT_var, partial_products1[i]->SAT_var, Y->SAT_var+i);
		// TODO how to get rid of new variables creation?!
		partial_products2[i]=gen_shift_left(ctx, partial_products1[i], i);
	};

	struct SMT_var *product=partial_products2[0];

	for (int i=1; i<w; i++)
		product=gen_BVADD(ctx, product, partial_products2[i]);

	// "ground" high part to 0?
	if (type==1)
		fix_BV_to_zero(ctx, product->SAT_var+w, w);

	// leave only low part of product, same width as in both inputs:
	return gen_extract(ctx, product, 0, w);
};

void add_Tseitin_OR (struct ctx* ctx, int a, int b, int out)
{
	add_clause3 (ctx, a, b, -out);
	add_clause2 (ctx, -a, out);
	add_clause2 (ctx, -b, out);
};

struct SMT_var* gen_OR(struct ctx* ctx, struct SMT_var* v1, struct SMT_var* v2)
{
	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BOOL, 1);
	add_comment (ctx, "gen_OR id1 (SMT) %s, id2 (SMT) %s, var1 (SAT) %d, var2 (SAT) %d, out id (SMT) %s, out var (SAT) %d",
		v1->id.c_str(), v2->id.c_str(), v1->SAT_var, v2->SAT_var, rt->id.c_str(), rt->SAT_var);

	add_Tseitin_OR (ctx, v1->SAT_var, v2->SAT_var, rt->SAT_var);

	return rt;
};

// selector, true, false, x (output)
void add_Tseitin_ITE (struct ctx* ctx, int s, int t, int f, int x)
{
	add_comment (ctx, __FUNCTION__);
        // as found by my util 
        add_clause3(ctx, -s, -t, x);
        add_clause3(ctx, -s, t, -x);
        add_clause3(ctx, s, -f, x);
	add_clause3(ctx, s, f, -x);
};

void add_Tseitin_ITE_BV (struct ctx* ctx, int s, int t, int f, int x, int width)
{
	for (int i=0; i<width; i++)
		add_Tseitin_ITE(ctx, s, t+i, f+i, x+i);
};

struct SMT_var* gen_ITE(struct ctx* ctx, struct SMT_var* sel, struct SMT_var* t, struct SMT_var* f)
{
	//assure_TY_BOOL("ite", sel);
	if (sel->width!=1)
		die ("line %d: ITE's selector must have width of 1 bit (no matter, bool or bitvec), but %d bits supplied\n", yylineno, sel->width);
/*
	assure_TY_BITVEC("ite", t);
	assure_TY_BITVEC("ite", f);
*/
	assure_eq_widths("ite", t, f);

	struct SMT_var* rt=create_internal_variable(ctx, "internal", TY_BITVEC, t->width);

	add_Tseitin_ITE_BV (ctx, sel->SAT_var, t->SAT_var, f->SAT_var, rt->SAT_var, t->width);

	return rt;
}

struct SMT_var* gen_binary (struct ctx* ctx, struct expr* e)
{
	assert (e->node_type==EXPR_BINARY);
	struct SMT_var* rt;

	struct SMT_var* v1=gen(ctx, e->op1);
	struct SMT_var* v2=gen(ctx, e->op2);
	switch (e->op)
	{
		case OP_EQ:		rt=gen_EQ (ctx, v1, v2); break;
		case OP_NEQ:		rt=gen_NEQ (ctx, v1, v2); break;
		case OP_OR:		rt=gen_OR (ctx, v1, v2); break;
		case OP_XOR:		rt=gen_XOR (ctx, v1, v2); break;
		case OP_AND:		rt=gen_AND (ctx, v1, v2); break;
		case OP_BVOR:		rt=gen_BVOR (ctx, v1, v2); break;
		case OP_BVXOR:		rt=gen_BVXOR (ctx, v1, v2); break;
		case OP_BVAND:		rt=gen_BVAND (ctx, v1, v2); break;
		case OP_BVADD:		rt=gen_BVADD (ctx, v1, v2); break;
		case OP_BVSUB:		rt=gen_BVSUB (ctx, v1, v2); break;
		case OP_BVMUL:		rt=gen_BVMUL (ctx, v1, v2, 0); break;
		case OP_BVMUL_NO_OVERFLOW:	rt=gen_BVMUL (ctx, v1, v2, 1); break;
		case OP_BVUGE:		rt=gen_BVUGE (ctx, v1, v2); break;
		case OP_BVULE:		rt=gen_BVULE (ctx, v1, v2); break;
		case OP_BVUGT:		rt=gen_BVUGT (ctx, v1, v2); break;
		case OP_BVULT:		rt=gen_BVULT (ctx, v1, v2); break;
		case OP_BVSGE:		rt=gen_BVSGE (ctx, v1, v2); break;
		case OP_BVSLE:		rt=gen_BVSLE (ctx, v1, v2); break;
		case OP_BVSGT:		rt=gen_BVSGT (ctx, v1, v2); break;
		case OP_BVSLT:		rt=gen_BVSLT (ctx, v1, v2); break;
		case OP_BVSUBGE:
					{
						struct SMT_var *output;
						struct SMT_var *cond;
						gen_BVSUBGE (ctx, ctx->var_always_true, v1, v2, &output, &cond);
						output->e=e;
						return output;
					};
		case OP_BVUDIV:		rt=gen_BVUDIV (ctx, v1, v2); break;
		case OP_BVUREM:		rt=gen_BVUREM (ctx, v1, v2); break;
		case OP_BVSHL:		rt=gen_BVSHL (ctx, gen (ctx, e->op1), gen (ctx, e->op2)); break;
		case OP_BVLSHR:		rt=gen_BVLSHR (ctx, gen (ctx, e->op1), gen (ctx, e->op2)); break;
		case OP_BVASHR:		rt=gen_BVASHR (ctx, gen (ctx, e->op1), gen (ctx, e->op2)); break;
		default:		assert(0);
	}
	rt->e=e;
	return rt;
};


struct SMT_var* gen(struct ctx* ctx, struct expr* e)
{
	if (verbose)
	{
		printf ("%s() begin ", __FUNCTION__);
		print_expr(e);
		printf ("\n");
	};

	struct SMT_var* rt;
		
	switch (e->node_type)
	{
		case EXPR_ID:
			rt=find_variable(ctx, e->id);
			if(rt==NULL)
				die ("line %d: variable %s hasn't been declared\n", yylineno, e->id);
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;

		case EXPR_CONST:
			rt=gen_const(ctx, e->const_val, e->width);
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;
	
		case EXPR_ZERO_EXTEND:
			rt=gen_zero_extend(ctx, gen(ctx, e->op1), e->const_val);
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;

		case EXPR_REPEAT:
			rt=gen_repeat(ctx, gen(ctx, e->op1), e->const_val);
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;

		case EXPR_EXTRACT:
			rt=gen_extract(ctx, gen(ctx, e->op1), e->const_val, e->width);
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;

		case EXPR_UNARY:
			switch (e->op)
			{
				case OP_NOT:		rt=gen_NOT (ctx, gen (ctx, e->op1)); break;
				case OP_BVNOT:		rt=gen_BVNOT (ctx, gen (ctx, e->op1)); break;
				case OP_BVNEG:		rt=gen_BVNEG (ctx, gen (ctx, e->op1)); break;
				case OP_BVSHL1:		rt=gen_shift_left (ctx, gen (ctx, e->op1), 1); break;
				case OP_BVSHR1:		rt=gen_shift_right (ctx, gen (ctx, e->op1), 1, ctx->var_always_false->SAT_var); break;
				default:		assert(0);
			};
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;
	
		case EXPR_BINARY:
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return gen_binary(ctx, e);

		case EXPR_TERNARY:
			assert (e->op==OP_ITE);

			rt=gen_ITE(ctx, gen(ctx, e->op1), gen(ctx, e->op2), gen(ctx, e->op3));
			rt->e=e;
			if (verbose)
				printf ("%s:%d end\n", __FUNCTION__, __LINE__);
			return rt;

		default:
			assert(0);
	};
};

void create_assert (struct ctx* ctx, struct expr* e)
{
	if (verbose)
	{
		printf ("%s() ", __FUNCTION__);
		print_expr(e);
		printf ("\n");
	};

	// small optimization, however, can't get serious boost...
	// if expression has form (assert (= x y)), use add_Tseitin_EQ_bitvecs here
	if (e->node_type==EXPR_BINARY && e->op==OP_EQ)
	{
		struct SMT_var *op1=gen(ctx, e->op1);
		struct SMT_var *op2=gen(ctx, e->op2);
/*
		printf ("optimized\n");
		printf ("op1. id==%s, e=", op1->id); print_expr(op1->e); printf ("\n");
		printf ("op2. id==%s, e=", op2->id); print_expr(op2->e); printf ("\n");
*/
		assure_eq_widths(__FUNCTION__, op1, op2);

		add_Tseitin_EQ_bitvecs(ctx, op1->width, op1->SAT_var, op2->SAT_var);
		return;
	}

	// otherwise, EQ will be generated and "grounded" to True,
	// which can be inefficient, because EQ is NOT-OR-XOR
	struct SMT_var* v=gen(ctx, e);
	add_comment (ctx, "%s() id=%s var=%d", __FUNCTION__, v->id.c_str(), v->SAT_var);
	add_clause1 (ctx, v->SAT_var); // "ground" v to True
};

void create_min_max (struct ctx* ctx, struct expr* e, int min_max)
{
	if (ctx->create_min_max_called)
		die ("Due to limitations of MK85, only one minimize/maximize command is allowed\n");

	struct SMT_var* v=gen(ctx, e);

	assure_TY_BITVEC(__FUNCTION__, v);

	// if "minimize", negate input value:
	if (min_max==0)
		v=gen_BVNEG(ctx, v);

	add_comment (ctx, "%s(min_max=%d) id=%s var=%d", __FUNCTION__, min_max, v->id.c_str(), v->SAT_var);

	// maximize always. if we need to minimize, $v$ is already negated at this point:
	for (int i=0; i<v->width; i++)
		add_soft_clause1(ctx, /* weight */ 1UL<<i, v->SAT_var+i);

	ctx->create_min_max_called=true;
};

void write_CNF(struct ctx* ctx, const char *fname)
{
	uint32_t hard_clause_weight;

	if (ctx->maxsat)
		hard_clause_weight=ctx->max_weight+1;

	FILE* f=fopen (fname, "wt");
	assert (f!=NULL);
	if (ctx->maxsat)
		fprintf (f, "p wcnf %d %d %u\n", ctx->SAT_next_var_no-1, ctx->clauses_t, hard_clause_weight);
	else
		fprintf (f, "p cnf %d %d\n", ctx->SAT_next_var_no-1, ctx->clauses_t);
	for (auto c : ctx->clauses)
	{
		if (c.type==SOFT_CLAUSE)
		{
			assert(ctx->maxsat);
			//std::string s=cxx_list_of_ints_to_string(c.li);
			std::string s=cxx_list_of_vectors_to_string(c.li);
			fprintf (f, "%u %s 0\n", c.weight, s.c_str());
		}
		else if (c.type==HARD_CLASUE)
		{
			//std::string s=cxx_list_of_ints_to_string(c.li);
			std::string s=cxx_list_of_vectors_to_string(c.li);
			if (ctx->maxsat)
				fprintf (f, "%u %s 0\n", hard_clause_weight, s.c_str());
			else
				fprintf (f, "%s 0\n", s.c_str());
		}
		else if (c.type==COMMENT)
		{
			fprintf (f, "%s\n", c.s.c_str());
		};
	};
	fclose (f);
};

uint32_t SAT_solution_to_value(int* a, int w)
{
	int rt=0;
	for (int i=0; i<w; i++)
		if (a[i]>0)
			rt|=1<<i;
	return rt;
};

void fill_variables_from_SAT_solver_response(struct ctx* ctx, int *array)
{
	for (auto i : ctx->vars)
	{
		struct SMT_var* v=i.second;
		// do not set internal variables, for faster results:
		if (ctx->dump_internal_variables==false && v->internal)
			continue;

		v->val=SAT_solution_to_value(&array[v->SAT_var-1], v->width);
	};
};

bool run_minisat_and_get_solution(struct ctx* ctx)
{
	write_CNF (ctx, "tmp.cnf");

	unlink ("result.txt");
	int rt=system ("./Linux-x86/minisat tmp.cnf result.txt > /dev/null");
	if (rt==32512)
		die ("Error: minisat executable not found.\n");

	// parse SAT response:

	size_t buflen=ctx->SAT_next_var_no*10;
	char *buf=(char*)xmalloc(buflen);
	assert(buf);

	FILE* f=fopen ("result.txt", "rt");
	assert (fgets (buf, buflen, f)!=NULL);
	if (strncmp (buf, "SAT", 3)==0)
	{
		assert (fgets (buf, buflen, f)!=NULL);
		//printf ("2nd line: %s\n", buf);
		size_t total;
		// TODO make use of the fact that list is sorted!
		ctx->solution=list_of_numbers_to_array(buf, ctx->SAT_next_var_no, &total);
		fill_variables_from_SAT_solver_response(ctx, ctx->solution);
		fclose (f);
		return true;
	}
	else if (strncmp (buf, "UNSAT", 5)==0)
	{
		fclose (f);
		return false;
	}
	else if (strncmp (buf, "INDET", 5)==0)
	{
		printf ("minisat has been interrupted.\n");
		exit(0);
	}
	else
	{
		fclose (f);
		die ("Fatal error. 1st line of minisat's answer unparsed: %s\n", buf);
	}
	return false; // make compiler happy
};

void add_clauses_to_picosat(struct ctx* ctx, struct PicoSAT *p)
{
	if (verbose)
		printf ("%s() begin. ctx->clauses.size()=%lld\n", __FUNCTION__, ctx->clauses.size());

	for (auto c : ctx->clauses)
	{
		if (c.type==HARD_CLASUE)
		{
			for (auto i : c.li)
				picosat_add (p, i);
			picosat_add(p, 0);
		}
	};
	if (verbose)
		printf ("%s() end\n", __FUNCTION__);
};

int* fill_variables_from_picosat(struct ctx* ctx, struct PicoSAT *p)
{
	int *array=(int*)xmalloc(sizeof(int)*(ctx->SAT_next_var_no-1));
	for (int i=0; i<ctx->SAT_next_var_no-1; i++)
		array[i]=picosat_deref(p, i+1);
	fill_variables_from_SAT_solver_response(ctx, array);
	//xfree(array);
	return array;
};

bool run_picosat_and_get_solution(struct ctx* ctx)
{
	if (verbose>0)
		printf ("%s() begin\n", __FUNCTION__);
	assert (ctx->maxsat==false);
	struct PicoSAT *p=picosat_init ();

	add_clauses_to_picosat(ctx, p);

	if (ctx->write_CNF_file)
	{
		write_CNF(ctx, "tmp.cnf");
		printf ("CNF file written to tmp.cnf\n");
	};

	if (verbose>0)
		printf ("%s() going to call picosat_sat()\n", __FUNCTION__);
	int res=picosat_sat (p,-1);
	if (res==20)
		return false;
	else if (res==10)
	{
		fill_variables_from_picosat(ctx, p);
		picosat_reset(p);
		return true;
	}
	else
	{
		assert(0);
	};
};

bool run_SAT_solver_and_get_solution(struct ctx* ctx)
{
	//return run_minisat_and_get_solution();
	return run_picosat_and_get_solution(ctx);
};

bool run_WBO_solver_and_get_solution(struct ctx* ctx)
{
	write_CNF (ctx, "tmp.wcnf");

	unlink ("result.txt");
	int rt=system ("./Linux-x86/open-wbo tmp.wcnf > result.txt");
	if (rt==32512)
		die ("Error: open-wbo executable not found.\n");

	// parse SAT response:

	size_t buflen=ctx->SAT_next_var_no*10;
	char *buf=(char*)xmalloc(buflen);
	assert(buf);

	FILE* f=fopen ("result.txt", "rt");
	while (fgets (buf, buflen, f)!=NULL)
	{
		if (buf[0]=='s')
		{
			if (memcmp (buf, "s UNSAT", 7)==0)
				return false;
		}
		else if (buf[0]=='v')
		{
			size_t total;
			ctx->solution=list_of_numbers_to_array(buf+2, ctx->SAT_next_var_no, &total);
			fill_variables_from_SAT_solver_response(ctx, ctx->solution);
			fclose (f);
			return true;
		};
	};

	return false; // make compiler happy
};

int check_sat(struct ctx* ctx)
{
	bool rt;

	if (ctx->maxsat)
		rt=run_WBO_solver_and_get_solution(ctx);
	else
		rt=run_SAT_solver_and_get_solution(ctx);

	ctx->sat=rt;
	return rt;
};

void get_model(struct ctx* ctx)
{
	if (ctx->sat)
		dump_all_variables(ctx, ctx->dump_internal_variables);
	else
		printf ("(error \"model is not available\")\n");
}

void negate_solution_and_add_as_constraint(struct ctx* ctx, int *solution)
{
	negate_all_elements_in_int_array(solution);
	add_comment(ctx, "negated solution");
	class clause c;
	c.type=HARD_CLASUE;
	for (int i=0; solution[i]; i++)
		c.li.push_back(solution[i]);
	ctx->clauses.push_back(c);
	ctx->clauses_t++;
};

void minisat_get_all_models(struct ctx* ctx, bool dump_variables)
{
	int total=0;
	while (run_minisat_and_get_solution(ctx))
	{
		total++;
		if (verbose>0 && (total&0xff)==0)
			printf ("(Heartbeat) %d models already\n", total);
		if (dump_variables)
			dump_all_variables(ctx, ctx->dump_internal_variables);
		negate_solution_and_add_as_constraint(ctx, ctx->solution);

	};
	printf ("Model count: %d\n", total);
};

int picosat_get_all_models(struct ctx* ctx, bool dump_variables, bool print_model_count)
{
	assert (ctx->maxsat==false);
	int total=0;
	struct PicoSAT *p=picosat_init ();

	add_clauses_to_picosat(ctx, p);

	int res;

	while ((res=picosat_sat(p,-1))==10)
	{
		total++;
		if (verbose>0 && (total&0xff)==0)
			printf ("(Heartbeat) %d models already\n", total);
		int *solution=fill_variables_from_picosat(ctx, p);
		if (dump_variables)
			dump_all_variables(ctx, ctx->dump_internal_variables);

		for (int v=0; v<ctx->SAT_next_var_no-1; v++)
		{
			// add negated:
			if (solution[v]<0)
				picosat_add(p, v+1);
			else
				picosat_add(p, -(v+1));
		};
		picosat_add(p, 0);
	};
	picosat_reset(p);
	if (print_model_count)
		printf ("Model count: %d\n", total);
	return total;
};

void get_all_models(struct ctx* ctx, bool dump_variables)
{
	//minisat_get_all_models(dump_variables);
	picosat_get_all_models(ctx, dump_variables, true);
};

unsigned int count_models(struct ctx* ctx)
{
	return picosat_get_all_models(ctx, false, false);
};

struct ctx* MK85_init()
{
	struct ctx* ctx=new (struct ctx);

	ctx->SAT_next_var_no=1;
	ctx->next_internal_var=1;
	ctx->dump_internal_variables=false;
	ctx->write_CNF_file=false;
	//ctx->write_CNF_file=true;
	ctx->clauses_t=0;
	ctx->max_weight=0;
	ctx->maxsat=false;
	ctx->create_min_max_called=false;
	ctx->sat=false;

	ctx->var_always_false=declare_variable(ctx, "always_false", TY_BOOL, 1, 1);
	add_comment (ctx, "always false");
	add_clause1(ctx, -ctx->var_always_false->SAT_var);
	add_comment (ctx, "always true");
	ctx->var_always_true=declare_variable(ctx, "always_true", TY_BOOL, 1, 1);
	add_clause1(ctx, ctx->var_always_true->SAT_var);

	return ctx;
};

struct expr* set_next(struct expr* arg, struct expr* n)
{
	arg->next=n;
	return n;
};

enum TY get_type_of_expr(struct expr* e)
{
	return e->type;
};

int get_width_of_expr(struct expr* e)
{
	return e->width;
};

