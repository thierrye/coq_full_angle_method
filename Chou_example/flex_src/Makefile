all : trad

trad : trad.c
	gcc -o trad trad.c -lfl -g

trad.c : trad.lex
	flex -o trad.c trad.lex


clean :
	rm -f *~ trad.c trad 
