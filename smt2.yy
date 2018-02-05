%{
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "MK85.hh"
#include "utils.hh"

int yylex(void);
void yyerror(const char *);

%}

%union
{
	char* text;
	int i;
	struct expr* e;
}

%token T_L_PAREN T_R_PAREN T_UNDERSCORE T_DOT
%token T_SET_LOGIC T_SET_INFO T_DECLARE_FUN T_ASSERT T_CHECK_SAT T_GET_MODEL T_QF_BV T_BVNOT T_BVNEG T_GET_ALL_MODELS
%token T_MAXIMIZE T_MINIMIZE
%token T_COUNT_MODELS
%token T_SMT_LIB_VERSION
%token T_NUMBER T_ID T_TEXT T_CONST T_BV_DEC_CONST
%token T_BOOL T_BITVEC
%token T_EQ T_NOT T_OR T_XOR T_AND T_BVXOR T_BVADD T_BVAND T_BVOR T_BVSUB T_BVMUL T_BVMUL_NO_OVERFLOW T_BVUDIV T_BVUREM
%token T_BVUGE T_BVULE T_BVUGT T_BVULT T_DISTINCT T_BVSHL T_BVLSHR T_BVASHR T_BVSHL1 T_BVSHR1 T_BVSUBGE
%token T_WHITESPACE
%token T_ZERO_EXTEND T_EXTRACT T_REPEAT T_ITE

%type <text> T_ID
%type <i> T_NUMBER
%type <i> T_BV_DEC_CONST
%type <i> unary_func
%type <i> binary_func
%type <i> vararg_func
%type <e> expr
%type <e> expr_list
%type <e> T_CONST

%error-verbose

%%

file:	commandline file
	| commandline
	;

commandline: T_L_PAREN T_SET_LOGIC T_QF_BV T_R_PAREN
        | T_L_PAREN T_SET_INFO T_SMT_LIB_VERSION T_NUMBER T_DOT T_NUMBER T_R_PAREN
        | T_L_PAREN T_DECLARE_FUN T_ID T_L_PAREN T_R_PAREN T_BOOL T_R_PAREN
	{
		create_variable($3, TY_BOOL, 1, 0);
	}
        | T_L_PAREN T_DECLARE_FUN T_ID T_L_PAREN T_R_PAREN T_L_PAREN T_UNDERSCORE T_BITVEC T_NUMBER T_R_PAREN T_R_PAREN
	{
		create_variable($3, TY_BITVEC, $9, 0);
	}
        | T_L_PAREN T_ASSERT expr T_R_PAREN
	{
		create_assert($3);
	}
        | T_L_PAREN T_MINIMIZE expr T_R_PAREN
	{
		create_min_max($3, false);
	}
        | T_L_PAREN T_MAXIMIZE expr T_R_PAREN
	{
		create_min_max($3, true);
	}
        | T_L_PAREN T_CHECK_SAT T_R_PAREN
	{
		check_sat();
	}
        | T_L_PAREN T_GET_MODEL T_R_PAREN
	{
		get_model();
	}
        | T_L_PAREN T_GET_ALL_MODELS T_R_PAREN
	{
		get_all_models(true);
	}
        | T_L_PAREN T_COUNT_MODELS T_R_PAREN
	{
		get_all_models(false);
	}
        ;

unary_func:
	T_NOT		{ $$=OP_NOT; }
	| T_BVNOT	{ $$=OP_BVNOT; }
	| T_BVNEG	{ $$=OP_BVNEG; }
	| T_BVSHL1	{ $$=OP_BVSHL1; }
	| T_BVSHR1	{ $$=OP_BVSHR1; }
	;

binary_func:
	T_BVSUBGE	{ $$=OP_BVSUBGE; }
	| T_EQ		{ $$=OP_EQ; }
	| T_BVUGE	{ $$=OP_BVUGE; }
	| T_BVULE	{ $$=OP_BVULE; }
	| T_BVUGT	{ $$=OP_BVUGT; }
	| T_BVULT	{ $$=OP_BVULT; }
	| T_BVUDIV	{ $$=OP_BVUDIV; }
	| T_BVUREM	{ $$=OP_BVUREM; }
	| T_BVSHL	{ $$=OP_BVSHL; }
	| T_BVLSHR	{ $$=OP_BVLSHR; }
	| T_BVASHR	{ $$=OP_BVASHR; }
	;

vararg_func:
	T_OR		{ $$=OP_OR; }
	| T_XOR		{ $$=OP_XOR; }
	| T_AND		{ $$=OP_AND; }
	| T_BVOR	{ $$=OP_BVOR; }
	| T_BVXOR	{ $$=OP_BVXOR; }
	| T_BVAND	{ $$=OP_BVAND; }
	| T_BVADD	{ $$=OP_BVADD; }
	| T_BVSUB	{ $$=OP_BVSUB; }
	| T_BVMUL	{ $$=OP_BVMUL; }
	| T_BVMUL_NO_OVERFLOW	{ $$=OP_BVMUL_NO_OVERFLOW; }
	;

expr_list:	expr
		| expr_list expr
		{
			// this is important. provide left associativity:
			$2->next=$1;
			$$=$2;
		}
		;

expr:	T_ID
	{
		$$=(struct expr*)xmalloc(sizeof(struct expr));
		$$->type=EXPR_ID;
		$$->id=$1;
		$$->next=NULL;
	}
	| T_CONST
        | T_L_PAREN T_UNDERSCORE T_BV_DEC_CONST T_NUMBER T_R_PAREN
	{
		$$=create_const_expr($3, $4);
	}
        | T_L_PAREN T_L_PAREN T_UNDERSCORE T_ZERO_EXTEND T_NUMBER T_R_PAREN expr T_R_PAREN
	{
		$$=create_zero_extend_expr($5, $7);
	}
        | T_L_PAREN T_L_PAREN T_UNDERSCORE T_REPEAT T_NUMBER T_R_PAREN expr T_R_PAREN
	{
		$$=create_repeat_expr($5, $7);
	}
        | T_L_PAREN T_ITE expr expr expr T_R_PAREN
	{
		$$=create_ternary_expr(OP_ITE, $3, $4, $5);
	}
        | T_L_PAREN T_L_PAREN T_UNDERSCORE T_EXTRACT T_NUMBER T_NUMBER T_R_PAREN expr T_R_PAREN
	{
		$$=create_extract_expr($5, $6, $8);
	}
        | T_L_PAREN unary_func expr T_R_PAREN
	{
		$$=create_unary_expr((enum OP)$2, $3);
	}
        | T_L_PAREN binary_func expr expr T_R_PAREN
	{
		$$=create_bin_expr((enum OP)$2, $3, $4);
	}
        | T_L_PAREN vararg_func expr_list T_R_PAREN
	{
		$$=create_vararg_expr((enum OP)$2, $3);
	}
        | T_L_PAREN T_DISTINCT expr_list T_R_PAREN
	{
		$$=create_distinct_expr($3);
	}
        ;

%%

extern FILE* yyin;
extern int yylineno;

void yyerror(const char *s)
{
	fprintf(stderr, "bison error: %s at line %d\n", s, yylineno);
}

int main(int argc, char *argv[])
{
	int i;
	for (i=1; i<argc && argv[i][0]=='-'; i++)
	{
		// handle switches
		// TODO stricmp
		if (strcmp(argv[i], "--dump-internal-variables")==0)
			dump_internal_variables=true;
		if (strcmp(argv[i], "--write-CNF")==0)
			write_CNF_file=true;
	};

	if (i>=argc)
		die ("Usage: filename.smt\n");

	FILE* input = fopen(argv[i], "r");
	if (input==NULL)
	{
		printf ("Cannot open input file\n");
		return 0;
	} 

	init();

	yyin = input;

	do 
	{
		yyparse();
	}
	while (feof(yyin)==0);
};

