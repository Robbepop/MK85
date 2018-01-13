COPT=-Wall -g -c -O3
#COPT=-Wall -g -pg -c

all: MK85

MK85: lex.yy.o y.tab.o MK85.o utils.o
	#gcc MK85.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -lgc -g -pg -o MK85
	#gcc MK85.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -lgc -g -o MK85
	gcc MK85.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -g -o MK85

utils.o: utils.c utils.h
	gcc $(COPT) utils.c

lex.yy.c: smt2.l y.tab.h
	flex smt2.l
	#flex -d smt2.l

lex.yy.o: lex.yy.c
	gcc $(COPT) -DYYDEBUG=1 lex.yy.c

y.tab.h y.tab.c: smt2.y
	bison -y -d -t smt2.y

y.tab.o: y.tab.c y.tab.h
	gcc $(COPT) -DYYDEBUG=1 y.tab.c

MK85.o: MK85.c
	gcc $(COPT) MK85.c

clean:
	rm *.o
	rm lex.yy.c
	rm y.tab.c
	rm y.tab.h

