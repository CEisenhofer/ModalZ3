%{
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define YYMAXDEPTH 1000000

enum Flavour {
	ETRUE,
	EFALSE,
	EID,
	EBOX,
	EDIA,
	ENOT,
	EAND,
	EOR,
	EIMP,
	EEQV
};

struct Expr {
	enum Flavour flavour;
	const char *head;
	struct Expr *expr1;
	struct Expr *expr2;
};

#define YYSTYPE struct Expr

struct Expr *box_expr(struct Expr expr) {
	struct Expr *boxed = malloc(sizeof(expr));
	*boxed = expr;
	return boxed;
}

void print_expr(struct Expr expr) {
	switch(expr.flavour) {
	case ETRUE:
		printf("true");
		break;
	case EFALSE:
		printf("false");
		break;
	case EID:
		printf("(%s world)", expr.head);
		break;
	case EBOX:
		printf("(box r ");
		print_expr(*expr.expr1);
		printf(")");
		break;
	case EDIA:
		printf("(dia r ");
		print_expr(*expr.expr1);
		printf(")");
		break;
	case ENOT:
		printf("(not ");
		print_expr(*expr.expr1);
		printf(")");
		break;
	case EAND:
		printf("(and ");
		print_expr(*expr.expr1);
		printf(" ");
		print_expr(*expr.expr2);
		printf(")");
		break;
	case EOR:
		printf("(or ");
		print_expr(*expr.expr1);
		printf(" ");
		print_expr(*expr.expr2);
		printf(")");
		break;
	case EIMP:
		printf("(=> ");
		print_expr(*expr.expr1);
		printf(" ");
		print_expr(*expr.expr2);
		printf(")");
		break;
	case EEQV:
		printf("(= ");
		print_expr(*expr.expr1);
		printf(" ");
		print_expr(*expr.expr2);
		printf(")");
		break;
	}
}

int yylex(void);
extern const char *yytext;
extern unsigned yyleng;

void yyerror(const char *err) {
	fprintf(stderr, "err near: %s (%s)\n", yytext, err);
	exit(EXIT_FAILURE);
}

char **ids = NULL;
unsigned num_ids = 0;

%}

%token LPAREN
%token RPAREN
%token TRUE
%token FALSE
%token ID
%token NOT
%token AND
%token OR
%token IMP
%token EQV
%token BOX
%token DIA
%token START
%token END

%%
input : START optional_toplevel END {};

optional_toplevel : | toplevel {};

toplevel : unary {
	printf("(assert ");
	print_expr($1);
	printf(")\n");
};

binary: or | and | imp | eqv | unary;

or: unary OR binary {
	$$.flavour = EOR;
	$$.head = NULL;
	$$.expr1 = box_expr($1);
	$$.expr2 = box_expr($3);
}

and: unary AND binary {
	$$.flavour = EAND;
	$$.head = NULL;
	$$.expr1 = box_expr($1);
	$$.expr2 = box_expr($3);
}

imp: unary IMP unary {
	$$.flavour = EIMP;
	$$.head = NULL;
	$$.expr1 = box_expr($1);
	$$.expr2 = box_expr($3);
}

eqv: unary EQV unary {
	$$.flavour = EEQV;
	$$.head = NULL;
	$$.expr1 = box_expr($1);
	$$.expr2 = box_expr($3);
}

unary: box | dia | not | parens | id | bool;

box: BOX unary {
	$$.flavour = EBOX;
	$$.head = NULL;
	$$.expr1 = box_expr($2);
	$$.expr2 = NULL;
};

dia: DIA unary {
	$$.flavour = EDIA;
	$$.head = NULL;
	$$.expr1 = box_expr($2);
	$$.expr2 = NULL;
};

not: NOT unary {
	$$.flavour = ENOT;
	$$.head = NULL;
	$$.expr1 = box_expr($2);
	$$.expr2 = NULL;
};

parens: LPAREN binary RPAREN { $$ = $2; };

id: ID {
	char *id = NULL;
	bool exists = false;

	// try looking up existing identifier
	for(int i = 0; i < num_ids; i++) {
		exists = true;
		for(unsigned j = 0; ids[i][j] || j < yyleng; j++)
			if(!ids[i][j] || j == yyleng || ids[i][j] != yytext[j]) {
				exists = false;
				break;
			}
		if(exists) {
			id = ids[i];
			break;
		}
	}

	// new identifier
	if(!exists) {
		id = malloc(yyleng + 1);
		strncpy(id, yytext, yyleng);
		id[yyleng] = 0;
		ids = realloc(ids, sizeof(id) * (num_ids + 1));
		ids[num_ids++] = id;

		printf("(declare-fun %s (World) Bool)\n", id);
	}

	$$.flavour = EID;
	$$.head = id;
	$$.expr1 = NULL;
	$$.expr2 = NULL;
};

bool: true | false {
	$$.head = NULL;
	$$.expr1 = NULL;
	$$.expr2 = NULL;
}

true: TRUE { $$.flavour = ETRUE; }
false: FALSE { $$.flavour = EFALSE; }

%%

int main(int argc, char** argv) {
	printf("(declare-const r Relation)\n");
	if (argc == 2 && !strcmp(argv[1], "K4"))
		printf("(assert (trans r))\n");

	yyparse();
	return 0;
}
