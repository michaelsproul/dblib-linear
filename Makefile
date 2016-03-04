MAKEFLAGS=--no-print-directory

all: CoqMakefile
	make -f $^

CoqMakefile: _CoqProject
	coq_makefile -f $^ -o $@

clean: CoqMakefile
	make --quiet -f CoqMakefile clean

purge: clean
	rm -f CoqMakefile
