COPT=-Wall -g -c -O3
#COPT=-Wall -g -pg -c

all: MK85

MK85: lex.yy.o y.tab.o MK85.o utils.o
	#g++ MK85.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -g -pg -o MK85
	g++ MK85.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -g -o MK85

utils.o: utils.cc utils.hh
	g++ $(COPT) utils.cc

lex.yy.c: smt2.l y.tab.h
	flex smt2.l
	#flex -d smt2.l

lex.yy.o: lex.yy.c
	g++ $(COPT) -DYYDEBUG=1 lex.yy.c

y.tab.h y.tab.c: smt2.yy
	bison -y -d -t smt2.yy

y.tab.o: y.tab.c y.tab.h
	g++ $(COPT) -DYYDEBUG=1 y.tab.c

MK85.o: MK85.cc
	g++ $(COPT) MK85.cc

clean:
	rm *.o
	rm lex.yy.c
	rm y.tab.c
	rm y.tab.h

