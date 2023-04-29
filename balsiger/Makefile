all: balsiger

y.tab.c y.tab.h: balsiger.y
	$(YACC) -d $<

lex.yy.c: balsiger.l y.tab.h
	$(LEX) balsiger.l

balsiger: y.tab.o lex.yy.o
	$(CC) -Wl,--stack,16777216 -o $@ $^
