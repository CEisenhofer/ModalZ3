%option noyywrap
%{
#include "y.tab.h"
%}

start1 begin
end1 end
start2 sos\(formulas\)
end2 end_of_list
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
dot \.
ws [ \n]+

%%
{start1} return START1;
{end1} return END1;
{start2} return START2;
{end2} return END2;
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
{dot} return DOT;
{ws}
%%
