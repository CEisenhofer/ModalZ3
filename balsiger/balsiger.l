%option noyywrap
%{
#include "y.tab.h"
%}

start sos\(formulas\)
end end_of_list
lparen \(
rparen \)
not ~
and &
or \|
imp ->
box \[(r1)?\]
dia <(r1)?>
true true
false false
id [a-z][A-Za-z0-9]*
dot \.
ws [ \n]+

%%
{lparen} return LPAREN;
{rparen} return RPAREN;
{not} return NOT;
{and} return AND;
{or} return OR;
{imp} return IMP;
{box} return BOX;
{dia} return DIA;
{true} return TRUE;
{false} return FALSE;
{id} return ID;
{dot} return DOT;
{start} return START;
{end} return END;
{ws}
%%
