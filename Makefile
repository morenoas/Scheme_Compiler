MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.phony: %

%:
	cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o && mv $@ $(BASEDIR)

# usage:
# make -f ./compiler/Makefile foo = creates foo.s , run nasm on it , creates foo.o and executable foo.
# rm foo = clean ( = delete) foo.
# ./foo = run foo
# && = chains the above instructions.
# rm foo && make -f ./compiler/Makefile foo