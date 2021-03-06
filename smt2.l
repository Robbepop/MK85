%option yylineno

%{
#include "y.tab.h"
#include <stdlib.h>
#include <string.h>

#include "MK85.hh"
// die():
#include "utils.hh"

void yyerror(char *);
%}

%%

";".*		{ /* single-line comment, do nothing */ }
"("		{ return T_L_PAREN; }
")"		{ return T_R_PAREN; }
"_"		{ return T_UNDERSCORE; }
"."		{ return T_DOT; }
"set-logic"	{ return T_SET_LOGIC; }
"set-info"	{ return T_SET_INFO; }
"declare-fun"	{ return T_DECLARE_FUN; }
"assert"	{ return T_ASSERT; }
"minimize"	{ return T_MINIMIZE; }
"maximize"	{ return T_MAXIMIZE; }
"check-sat"	{ return T_CHECK_SAT; }
"get-all-models"	{ return T_GET_ALL_MODELS; }
"count-models"	{ return T_COUNT_MODELS; }
"get-model"	{ return T_GET_MODEL; }
"Bool"		{ return T_BOOL; }
"BitVec"	{ return T_BITVEC; }
"="		{ return T_EQ; }
"not"		{ return T_NOT; }
"or"		{ return T_OR; }
"xor"		{ return T_XOR; }
"and"		{ return T_AND; }
"bvnot"		{ return T_BVNOT; }
"bvneg"		{ return T_BVNEG; }
"bvxor"		{ return T_BVXOR; }
"bvadd"		{ return T_BVADD; }
"bvand"		{ return T_BVAND; }
"bvor"		{ return T_BVOR; }
"bvsub"		{ return T_BVSUB; }
"bvmul_no_overflow" { return T_BVMUL_NO_OVERFLOW; }
"bvmul"		{ return T_BVMUL; }
"bvudiv"	{ return T_BVUDIV; }
"bvurem"	{ return T_BVUREM; }
"bvugt"		{ return T_BVUGT; }
"bvuge"		{ return T_BVUGE; }
"bvule"		{ return T_BVULE; }
"bvult"		{ return T_BVULT; }
"bvsle"		{ return T_BVSLE; }
"bvslt"		{ return T_BVSLT; }
"bvsge"		{ return T_BVSGE; }
"bvsgt"		{ return T_BVSGT; }
"distinct"	{ return T_DISTINCT; }
"QF_BV"		{ return T_QF_BV; }
"zero_extend"	{ return T_ZERO_EXTEND; }
"repeat"	{ return T_REPEAT; }
"extract"	{ return T_EXTRACT; }
"ite"		{ return T_ITE; }
"bvshl"		{ return T_BVSHL; }
"bvlshr"	{ return T_BVLSHR; }
"bvashr"	{ return T_BVASHR; }
"bvshl1"	{ return T_BVSHL1; }
"bvshr1"	{ return T_BVSHR1; }
"bvsubge"	{ return T_BVSUBGE; }
":smt-lib-version" { return T_SMT_LIB_VERSION; }
bv[0-9]+	{
			if (sscanf(yytext+2, "%d", &yylval.i)!=1)
				die ("Fatal error: can't parse %s as a decimal number\n", yytext);

			return T_BV_DEC_CONST;
		}
#x[0-9a-fA-F]+	{
			uint32_t val;
			if (sscanf(yytext+2, "%x", &val)!=1)
				die ("Fatal error: can't parse %s as a hexadecimal number\n", yytext);

			int width=strlen(yytext+2)*4;
			//printf ("%s:%d width=%d\n", __FUNCTION__, __LINE__, width);
			yylval.e=create_const_expr(TY_BITVEC, val, width);
			return T_CONST;
		}

[a-zA-Z_]+[a-zA-Z0-9]* 	{
			yylval.text=xstrdup(yytext);
			return T_ID;
		}
[0-9]+		{
			if (sscanf(yytext, "%d", &yylval.i)!=1)
				die ("Fatal error: can't parse %s as a decimal number\n", yytext);

			return T_NUMBER;
		}



[ \n\r\t]       ;       /* skip whitespace */

.           printf("(lex/flex) unknown character: %c\n", yytext[0]);

%%

int yywrap(void)
{
	return 1;
}

void flex_set_str(char *s)
{
	YY_BUFFER_STATE buf;
	buf=yy_scan_string (s);
	yy_switch_to_buffer (buf);
};

void flex_cleanup()
{
	yy_delete_buffer( YY_CURRENT_BUFFER );
};

