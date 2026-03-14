
EXE=./minigo.exe

check: $(EXE)
	cd tests && ./test -1 ../minigo.exe
	cd tests && ./test -2 ../minigo.exe
	cd tests && ./test -3 ../minigo.exe
	
test: $(EXE) test.go
	go run test.go
	$(EXE) --debug test.go
	gcc -g -no-pie test.s -o test
	./test

$(EXE): *.ml*
	dune build @all

.PHONY: clean test check
clean:
	dune clean
