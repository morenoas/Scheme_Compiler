Scheme compiler to assembly X64 using OCaml programming language.

# usage:
  1. clone the repository.
  1. create a scheme file called foo.scm containing a scheme code to compile and run, and save it at the same level of where you saved the repository Scheme_Compiler.
  2. open a terminal in the directory where you just saved foo.scm and compile it by execute "make -f ./Scheme_Compiler/Makefile foo".
  3. run it by execute "./foo".

# details:
- make -f ./Scheme_Compiler/Makefile foo => creates foo.s , runs nasm on it , creates foo.o and executable foo.
- rm foo => clean ( = delete) foo.
- ./foo => run foo
- && => chains the above instructions.
- rm foo && make -f ./Scheme_Compiler/Makefile foo.
