
TRAM: TRAM.1.c
	gcc -o TRAM.1 TRAM.1.c

clean:
	rm *.out *.trm
	
test: TRAM
	cp test test.bak # make deletes file on occasion
	bash ./test TRAM.1
