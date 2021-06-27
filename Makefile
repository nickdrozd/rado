all : test

run : clean
	idris2 --version
	idris2 Run.idr -o run
	time -p ./build/exec/run

test : clean
	idris2 --version
	idris2 Test.idr -o test
	time -p ./build/exec/test

clean :
	rm -rf build/
