%option noyywrap
%{
#include "y.tab.h"
%}

start begin|(sos\(formulas\)\.)
end end|end_of_list
lparen \(
rparen \)
not ~
and &
or \|
imp ->
eqv <->
box \[(r1)?\]
dia <(r1)?>
true true
false false
id [a-z][A-Za-z0-9]*
ws [ \n]+

%%
{start} return START;
{end} return END;
{lparen} return LPAREN;
{rparen} return RPAREN;
{not} return NOT;
{and} return AND;
{or} return OR;
{imp} return IMP;
{eqv} return EQV;
{box} return BOX;
{dia} return DIA;
{true} return TRUE;
{false} return FALSE;
{id} return ID;
{ws}
%%
