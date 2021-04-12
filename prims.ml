(* 
   This module contains code to generate the low-level implementation of
   parts of the standard library procedures.
   The module works by defining a hierarchy of templates, which call each other
   to form complete routines. See the inline comments below for more information
   on the templates and the individual routines.

   Note that the implementation below contain no error handling or correctness-checking
   of any kind. This is because we will not test your compilers on invalid input.
   However, adding correctness-checking and error handling *as general templates* would be
   rather simple.
 *)
 module type PRIMS = sig
  val procs : string;;
end

module Prims : PRIMS = struct
  (* This is the most basic routine template. It takes a body and label name, and
     creates the standard x86-64 bit routine form.
     All other templates and routine-generation functions depend on this template. *)
  let make_routine label body =
    label ^ ":
       push rbp
       mov rbp, rsp 
       " ^ body ^ "
         pop rbp
         ret";;

  (* Many of the low-level stdlib procedures are predicate procedures, which perform 
     some kind of comparison, and then return one of the constants sob_true or sob_false.
     Since this pattern repeats so often, we have a template that takes a body, and a type
     of condition to test for jump, and generates an assembly snippet that evaluated the body,
     and return true or false, depending on the type of condition. *)
  let return_boolean jcc body =
    body ^ "
      " ^ jcc ^ " .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:";;

  (* 
     Many of the predicates just test some kind of equality (or, equivalently, if the 
     zero flag is set), so this is an auxiliary function dedicated to equality-testing predicates. 
     Note how we make use of currying here.
   *)
  let return_boolean_eq = return_boolean "je";;
  
  (* 
     Almost all of the stdlib function take 1 or more arguments. Since all of the variadic procedures
     are implemented in the high-level scheme library code (found in stdlib.scm), we only have to deal
     with 1,2 or 3 arguments.
     These helper functions inject instructions to get parameter values off the stack and into registers
     to work with.
     The argument register assignment follows the x86 64bit Unix ABI, because there needs to be *some*
     kind of consistency, so why not just use the standard ABI.
     See page 22 in https://raw.githubusercontent.com/wiki/hjl-tools/x86-psABI/x86-64-psABI-1.0.pdf

     *** FIXME: There's a typo here: PVAR(0) should be rdi, PVAR(1) should be rsi, according to the ABI     
   *)
  let make_unary label body = make_routine label ("mov rsi, PVAR(0)\n\t" ^ body);;
  let make_binary label body = make_unary label ("mov rdi, PVAR(1)\n\t" ^ body);;
  let make_tertiary label body = make_binary label ("mov rdx, PVAR(2)\n\t" ^ body);;

  (* All of the type queries in scheme (e.g., null?, pair?, char?, etc.) are equality predicates
     that are implemented by comparing the first byte pointed to by PVAR(0) to the relevant type tag.
     so the only unique bits of each of these predicates are the name of the routine (i.e., the label), 
     and the type tag we expect to find.
     The implementation of the type-queries generator is slightly more complex, since a template and a label
     name aren't enough: we need to generate a routine for every (label * type_tag) pair (e.g., the routine 
     `is_boolean` should test for the T_BOOL type tag).
     We have a list of pairs, associating each predicate label with the correct type tag, and map the templating 
     function over this list. Note that the query template function makes use of some of the other templating 
     functions defined above: `make_unary` (predicates take only one argument) and `return_boolean_eq` (since 
     these are equality-testing predicates).
   *)
  let type_queries =
    let queries_to_types = [
        "boolean", "T_BOOL"; "flonum", "T_FLOAT"; "rational", "T_RATIONAL"; "pair", "T_PAIR";
        "null", "T_NIL"; "char", "T_CHAR"; "string", "T_STRING"; "symbol", "T_SYMBOL";
        "procedure", "T_CLOSURE"
      ] in
    let single_query name type_tag =
      make_unary (name ^ "?")
        (return_boolean_eq ("mov sil, byte [rsi]\n\tcmp sil, " ^ type_tag)) in
    String.concat "\n\n" (List.map (fun (a, b) -> single_query a b) queries_to_types);;

  (* The rational number artihmetic operators have to normalize the fractions they return,
     so a GCD implementation is needed. Now there are two options: 
     1) implement only a scheme-procedure-like GCD, and allocate rational number scheme objects for the 
        intermediate numerator and denominator values of the fraction to be returned, call GCD, decompose
        the returned fraction, perform the divisions, and allocate the final fraction to return
     2) implement 2 GCDs: a low-level gcd that only implements the basic GCD loop, which is used by the rational 
        number arithmetic operations; and a scheme-procedure-like GCD to be wrapped by the stdlib GCD implementation.
    
     The second option is more efficient, and doesn't cost much, in terms of executable file bloat: there are only 4
     routines that inline the primitive gcd_loop: add, mul, div, and gcd.
     Note that div the inline_gcd embedded in div is dead code (the instructions are never executed), so a more optimized
     version of prims.ml could cut the duplication down to only 3 places (add, mul, gcd).
   *)
  let inline_gcd =
    ".gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:";;

  (* The arithmetic operation implementation is multi-tiered:
     - The low-level implementations of all operations are binary, e.g. (+ 1 2 3) and (+ 1) are not 
       supported in the low-level implementation.
     - The low-level implementations only support same-type operations, e.g. (+ 1 2.5) is not supported
       in the low-level implementation. This means each operation has two low-level implementations, one
       for floating-point operands, and one for fractional operands.
     - Each pair of low-level operation implementations is wrapped by a dispatcher which decides which 
       of the two implementations to call (by probing the types of the operands).
     - The high-level implementations (see stdlib.scm) make use of a high-level dispatcher, that is in charge
       of performing type conversions as necessary to satisfy the pre-conditions of the low-level implementations.
     
     Operations on floating-point operands:
     -------------------------------------
     The implementations of binary floating point arithmetic operations contain almost identical code. The
     differences are the name (label) of the routines, and the arithmetic instruction applied to 
     the two arguments. Other than that, they are all the same: binary routines which load the values
     pointed at by PVAR(0) and PVAR(1) into SSE2 registers, compute the operation, create a new sob_float
     on the heap with the result, and store the address of the sob_float in rax as the return value.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).

     Operations on fractional operands:
     ----------------------------------
     The addition and multiplication operations on rational numbers are similar to each other: both load 2 arguments,
     both deconstruct the arguments into numerator and denominator, both allocate a sob_rational to store the result
     on the heap, and both move the address of this sob_rational into rax as the return value. The only differences 
     are the routine name (label), and the implementation of the arithmetic operation itself.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).
     
     Unlike in the case of floating point arithmetic, rational division is treated differently, and is implemented by
     using the identity (a/b) / (c/d) == (a/b) * (d/c).
     This is done by inverting the second arg (in PVAR(1)) and tail-calling fraction multiplication (`jmp mul`).

     Comparators:
     ------------
     While the implementation of the Comparators is slightly more complex, since they make use of `return_boolean`,
     the idea is the same as the arithmetic operators.
     A couple of things to note:
     - `eq.flt` can collapse to a bitwise comparison (like in the case of integers in C), while `eq.rat` involves
       comparing the numerator and denominator separately, due to our fraction representation using 128 bits
       and not 64 bits.
     - `lt.flt` does not handle NaN, +inf and -inf correctly. This allows us to use `return_boolean jl` for both the
       floating-point and the fraction cases. For a fully correct implementation, `lt.flt` should make use of
       the `ucomisd` opcode and `return_boolean jb` instead (see https://www.felixcloutier.com/x86/ucomisd for
       more information).
   *)
  let numeric_ops =
    let numeric_op name flt_body rat_body body_wrapper =      
      make_binary name
        (body_wrapper
           ("mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne ." ^ name ^ "_rat
             " ^ flt_body ^ "
             jmp .op_return
          ." ^ name ^ "_rat:
             " ^ rat_body ^ "
          .op_return:")) in      
    let arith_map = [
        "MAKE_RATIONAL(rax, rdx, rdi)
         mov PVAR(1), rax
         pop rbp
         jmp mul", "divsd", "div";
        
        "imul rsi, rdi
	 imul rcx, rdx", "mulsd", "mul";
        
        "imul rsi, rdx
	 imul rdi, rcx
	 add rsi, rdi
	 imul rcx, rdx", "addsd", "add";
      ] in
    let arith name flt_op rat_op =
      numeric_op name
        ("FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  " ^ flt_op ^ " xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)")
        ("DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          " ^ rat_op ^ "
	  mov rax, rcx
	  mov rdi, rsi
          " ^ inline_gcd ^ "
	  mov rdi, rax
	  mov rax, rsi
	  cqo
	  idiv rdi
	  mov rsi, rax
	  mov rax, rcx
	  cqo
	  idiv rdi
	  mov rcx, rax
          cmp rcx, 0
          jge .make_rat
          imul rsi, -1
          imul rcx, -1
          .make_rat:
          MAKE_RATIONAL(rax, rsi, rcx)") in
    let comp_map = [
        (* = *)
        return_boolean_eq,
        "NUMERATOR rcx, rsi
	 NUMERATOR rdx, rdi
	 cmp rcx, rdx
	 jne .false
	 DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 cmp rcx, rdx
         .false:",
        "FLOAT_VAL rsi, rsi
	 FLOAT_VAL rdi, rdi
	 cmp rsi, rdi", "eq";

        (* < *)
        return_boolean "jl",
        "DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 NUMERATOR rsi, rsi
	 NUMERATOR rdi, rdi
	 imul rsi, rdx
	 imul rdi, rcx
	 cmp rsi, rdi",
        "FLOAT_VAL rsi, rsi
	 movq xmm0, rsi
	 FLOAT_VAL rdi, rdi
	 movq xmm1, rdi
	 cmpltpd xmm0, xmm1
         movq rsi, xmm0
         cmp rsi, 0", "lt";
      ] in
    let comparator comp_wrapper name flt_body rat_body = numeric_op name flt_body rat_body comp_wrapper in
    (String.concat "\n\n" (List.map (fun (a, b, c) -> arith c b a (fun x -> x)) arith_map)) ^
      "\n\n" ^
        (String.concat "\n\n" (List.map (fun (a, b, c, d) -> comparator a d c b) comp_map));;


  (* The following set of operations contain fewer similarities, to the degree that it doesn't seem that 
     creating more fine-grained templates for them is beneficial. However, since they all make use of
     some of the other templates, it is beneficial to organize them in a structure that enables
     a uniform mapping operation to join them all into the final string.*)
  let misc_ops =
    let misc_parts = [
        (* string ops *)
        "STRING_LENGTH rsi, rsi
         MAKE_RATIONAL(rax, rsi, 1)", make_unary, "string_length";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         mov sil, byte [rsi]
         MAKE_CHAR(rax, sil)", make_binary, "string_ref";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         CHAR_VAL rax, rdx
         mov byte [rsi], al
         mov rax, SOB_VOID_ADDRESS", make_tertiary, "string_set";
        
        "NUMERATOR rsi, rsi
         CHAR_VAL rdi, rdi
         and rdi, 255
         MAKE_STRING rax, rsi, dil", make_binary, "make_string";
        
        "SYMBOL_VAL rsi, rsi
	 STRING_LENGTH rcx, rsi
	 STRING_ELEMENTS rdi, rsi
	 push rcx
	 push rdi
	 mov dil, byte [rdi]
	 MAKE_CHAR(rax, dil)
	 push rax
	 MAKE_RATIONAL(rax, rcx, 1)
	 push rax
	 push 2
	 push SOB_NIL_ADDRESS
	 call make_string
	 add rsp, 4*8
	 STRING_ELEMENTS rsi, rax   
	 pop rdi
	 pop rcx
	 cmp rcx, 0
	 je .end
         .loop:
	 lea r8, [rdi+rcx]
	 lea r9, [rsi+rcx]
	 mov bl, byte [r8]
	 mov byte [r9], bl
	 loop .loop
         .end:", make_unary, "symbol_to_string";

        (* the identity predicate (i.e., address equality) *)
        (return_boolean_eq "cmp rsi, rdi"), make_binary, "eq?";

        (* type conversions *)
        "CHAR_VAL rsi, rsi
	 and rsi, 255
	 MAKE_RATIONAL(rax, rsi, 1)", make_unary, "char_to_integer";

        "NUMERATOR rsi, rsi
	 and rsi, 255
	 MAKE_CHAR(rax, sil)", make_unary, "integer_to_char";

        "DENOMINATOR rdi, rsi
	 NUMERATOR rsi, rsi 
	 cvtsi2sd xmm0, rsi
	 cvtsi2sd xmm1, rdi
	 divsd xmm0, xmm1
	 movq rsi, xmm0
	 MAKE_FLOAT(rax, rsi)", make_unary, "exact_to_inexact";

        "NUMERATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "numerator";

        "DENOMINATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "denominator";

        (* GCD *)
        "xor rdx, rdx
	 NUMERATOR rax, rsi
         NUMERATOR rdi, rdi
         " ^ inline_gcd ^ "
	 mov rdx, rax
         cmp rdx, 0
         jge .make_result
         neg rdx
         .make_result:
         MAKE_RATIONAL(rax, rdx, 1)", make_binary, "gcd";  
      ] in
    String.concat "\n\n" (List.map (fun (a, b, c) -> (b c a)) misc_parts);;

  (* This is the interface of the module. It constructs a large x86 64-bit string using the routines
     defined above. The main compiler pipline code (in compiler.ml) calls into this module to get the
     string of primitive procedures. *)
  let procs = String.concat "\n\n" [type_queries ; numeric_ops; misc_ops] ^

            ";;;;;;;; added prim functions\n" ^ 

            "car:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              "mov rbx, PVAR(0)  ;; PVAR(0) = args[0] (this time a pair)\n\t" ^
              "CAR rax, rbx\n\t" ^
              "leave\n\t" ^
              "ret\n" ^

            "cdr:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              "mov rbx, PVAR(0)  ;; PVAR(0) = args[0] (this time a pair)\n\t" ^
              "CDR rax, rbx\n\t" ^
              "leave\n\t" ^
              "ret\n" ^

            "cons:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              "mov rbx, PVAR(0)              ;; PVAR(0) = args[0] (this time an object)\n\t" ^
              "mov rcx, PVAR(1)              ;; PVAR(1) = args[1] (this time an object)\n\t" ^
              "MAKE_PAIR(rax, rbx, rcx)\n\t" ^
              "leave\n\t" ^
              "ret\n" ^

            "set_car:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              "mov rbx, PVAR(0)              ;; rbx <- args[0] (this time a pair)\n\t" ^
              "mov rcx, PVAR(1)              ;; rcx <- = args[1] (this time an object)\n\t" ^
              "mov [rbx + TYPE_SIZE], rcx\n\t" ^
              "mov rax, SOB_VOID_ADDRESS\n\t" ^
              "leave\n\t" ^
              "ret\n" ^

            "set_cdr:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              "mov rbx, PVAR(0)              ;; rbx <- args[0] (this time a pair)\n\t" ^
              "mov rcx, PVAR(1)              ;; rcx <- = args[1] (this time an object)\n\t" ^
              "mov [rbx + TYPE_SIZE + WORD_SIZE], rcx\n\t" ^
              "mov rax, SOB_VOID_ADDRESS\n\t" ^
              "leave\n\t" ^
              "ret\n" ^

            "list_length:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^
              
              "mov rax, 0\n\t" ^
              (* "mov rbx, [rbx]      ;; rbx <- the list (because rbx first points to list)\n\t" ^ *)
              "loop:\n\t" ^
              "add rax, 1          ;; rax not empty (checked in apply)\n\t" ^
              "CDR rbx, rbx       ;; rbx <- cdr list\n\t" ^
              "cmp rbx, SOB_NIL_ADDRESS\n\t" ^
              "jne loop\n\t" ^

              "leave\n\t" ^
              "ret\n" ^

            "apply:\n\t" ^
              "push rbp\n\t" ^
              "mov rbp, rsp\n\t" ^

              ";;; 0. save old rbp ( = [rbp]), ret, proc. get list.length\n\t" ^
              (* no step 1 *)
              ";;; 2. make space on stack and ''push'' list elements \n\t" ^
              ";;; 3. push objects to stack,\n\t" ^
              (* no steps 4,5 *)
              ";;; 6. push number of total args\n\t" ^
              ";;; 7. check proc is closure, push env, push ret\n\t" ^
              ";;; 8. call proc.code\n\t" ^
              ";;; 9. clean stack frame (add rsp as in Applic)\n\t" ^
              ";;; 10. rbp <- old rbp\n" ^

            ";;; 0.\n\t" ^
              "mov r9, [rbp + 3 * WORD_SIZE]                 ;; r9 <- number of args ( = n)\n\t" ^
              "mov r8, r9                        ;; r8 <- number of args\n\t" ^
              "sub r9, 2                         ;; r9 <- number of objects\n\t" ^
              "mov rbx, PVAR(r9 + 1)             ;; rbx <- pointer to list (arg[n-1])\n\t" ^
              "mov r11, [rbp]                     ;; r11 <- old rbp\n\t" ^
              "mov r12, [rbp + 1 * WORD_SIZE]     ;; r12 <- ret address\n\t" ^
              "mov r13, PVAR(0)                   ;; r13 <- proc\n\t" ^

              "cmp rbx, SOB_NIL_ADDRESS\n\t" ^
              "je empty_list\n\t" ^
              "push rbx\n\t" ^
              "call list_length\n\t" ^
              "pop rbx\n\t" ^
              "mov r10, rax                       ;; r10 <- number of elements in list \n\t" ^
              "jmp after_length \n\t" ^
              "empty_list:\n\t" ^
              "mov r10, 0                         ;; r10 <- number of elements in list (case list is empty)\n" ^
              "after_length:\n" ^
            ";;; end 0.\n" ^
           
            ";;; 2.\n\t" ^
              "mov rcx, r10                   ;; rcx <- list.length\n\t" ^
              "shl r10, 3                     ;; r10 <- list.length * WORD_SIZE \n\t" ^
              "sub rsp, r10                   ;; make place on stack to list elements \n\t" ^
              "mov r10, 0                     ;; r10 <- 0 to (rcx -1)\n\t" ^
              
              "cmp rcx, 0\n\t" ^
              "je after_push_elements\n\t" ^
              "push_elements_of_list:\n\t" ^
              "CAR rax, rbx                   ;; rax <- car list\n\t" ^
              "                               ;; rdx <- rsp + r10 * WORD_SIZE\n\t" ^
              "mov rdx, r10                   ;; rdx <- r10\n\t" ^
              "shl rdx, 3                     ;; rdx <- r10 * WORD_SIZE\n\t" ^
              "add rdx, rsp                   ;; rdx <- rsp + r10 * WORD_SIZE\n\t" ^
              "mov [rdx], rax                 ;; ''pushing'' list elements \n\t" ^
              "CDR rbx, rbx                   ;; rbx <- cdr list\n\t" ^
              "add r10, 1\n\t" ^
              "loop push_elements_of_list\n\t" ^
              "after_push_elements:\n" ^
            ";;; end 2.\n" ^

            ";;; 3.\n\t" ^
              "mov rcx, r9                   ;; rcx <- number of objects\n\t" ^
              "cmp rcx, 0\n\t" ^
              "je after_push_objects\n\t" ^
              "push_objectst:\n\t" ^
              "push PVAR(rcx)                ;; (arg1,...argn-2) ((no arg0(=proc) and no argn-1(=list) ))\n\t" ^
              "loop push_objectst\n\t" ^
              "after_push_objects:\n" ^
            ";;; end 3.\n" ^

            ";;; 6.\n\t" ^
              "add r9, r10\n\t" ^
              "push r9\n" ^
            ";;; end 6.\n" ^
            ";;; 7.\n\t" ^
              "cmp byte [r13], T_CLOSURE      ;; r13 is proc, check this is a closure\n\t" ^  
              "je proc_is_closure\n" ^
            ";;; case proc doesn't have type closure\n" ^
            ";;; handle exception\n\t" ^
              "mov rax, 0\n\t" ^
              "leave\n\t" ^
              "ret\n\t" ^
              "proc_is_closure:\n\t" ^
              "CLOSURE_ENV rbx, r13\n\t" ^
              "push rbx\n\t" ^
              (* "push r12                       ;; r12 is ret address\n" ^ *)
            ";;; end 7.\n" ^
            ";;; 8.\n\t" ^
              "CLOSURE_CODE rbx, r13\n\t" ^
              "call rbx\n" ^
            ";;; end 8.\n" ^
            ";;; 9.\n\t" ^
              "add rsp , 8*1     ; pop env\n\t" ^
              "pop rbx           ; pop arg count\n\t" ^
              "shl rbx , 3       ; rbx = rbx * 8\n\t" ^
              "add rsp , rbx     ; pop args\n" ^
            ";;; end 9.\n" ^
            ";;; 10.\n\t" ^
              "pop rbp                  ;; r11 <- old rbp\n" ^
            ";;; end 10.\n\t" ^

              "ret\n" ^

            ";;;;;;;; finish added prim functions \n" ;;
end;;
