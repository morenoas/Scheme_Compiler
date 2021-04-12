
#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct


exception X_syntax_error;;
exception X_syntax_error1;;
exception X_syntax_error2;;





(* deletes duplications in l *)
  let rec makeSet l s = match l with
                    | [] -> [] 
                    | [a] -> if List.exists (fun e-> a = e) s then s else s @ [a]
                    | a::b -> if List.exists (fun e-> a = e) s then makeSet b s else makeSet b (s @ [a])
                    (* | _-> raise X_syntax_error1 *)
  ;;
  let rec makeConstsTablePerAST ast l = 
      match ast with
      | Const'(e) -> l @ [e]
      | Var'(_) | Box'(_) | BoxGet'(_) -> []
      | BoxSet'(_,exp) -> makeConstsTablePerAST exp l
      | If'(test, dit, dif) -> l @ (makeConstsTablePerAST test []) @ (makeConstsTablePerAST dit []) @ (makeConstsTablePerAST dif [])
      | Seq'(exps) -> List.fold_left (fun l1 l2 -> l1 @ (makeConstsTablePerAST l2 [])) l exps
      | Set'(_,exp) -> makeConstsTablePerAST exp l
      | Def'(_, exp) -> makeConstsTablePerAST exp l
      | Or'(exps) -> List.fold_left (fun l1 l2 -> l1 @ (makeConstsTablePerAST l2 [])) l exps
      | LambdaSimple'(args, body) -> makeConstsTablePerAST body l
      | LambdaOpt'(args, last, body) -> makeConstsTablePerAST body l
      | Applic'(e, exps) -> (makeConstsTablePerAST e []) @ (List.fold_left (fun l1 l2 -> l1 @ (makeConstsTablePerAST l2 [])) l exps)
      | ApplicTP'(e, exps) -> (makeConstsTablePerAST e []) @ (List.fold_left (fun l1 l2 -> l1 @ (makeConstsTablePerAST l2 [])) l exps)
  ;;
(* gets the offset of constant c in constants table*)
let rec getOffSet (c: sexpr) l = 
      match l with
      | [(Sexpr(se), (y, z))] -> if sexpr_eq se c then y else raise X_this_should_not_happen
      | (Void, (y, z))::b-> getOffSet c b 
      | (Sexpr(se), (y, z))::b-> if sexpr_eq se c then y else getOffSet c b 
      | _-> raise X_syntax_error
;;

let string_to_ascii_list str =
    let chars = string_to_list str in
    let asciis = List.map Char.code chars in
    let ascii_strs = List.map (Printf.sprintf "%d") asciis in
    String.concat "," ascii_strs;;

let make_unique_index label = 
    let last = ref (-1) in 
    (fun needToInc -> 
        if needToInc then incr last ;
        label ^ string_of_int !last)
    ;;

  let make_unique_str = make_unique_index "str" ;;
  let make_unique_end_str = make_unique_index "end_str" ;;

(* turns [sexpr1; sexpr2] into [(sexpr1, (0, "assembly code")); (sexpr2, (1, "assembly code"))] 
    nl = new list*)
  let rec getInternalConstsTable l i nl = 

    let labal_str_inc = make_unique_str true in
    let labal_str_no_inc = make_unique_str false in
    let labal_end_str_inc = make_unique_end_str true in
    let labal_end_str_no_inc = make_unique_end_str false in

      match l with
      | [] -> nl
      | [a] -> (match a with
                | Sexpr(Number(Fraction(num, denom))) -> nl @ [(a, (i, "MAKE_LITERAL_RATIONAL("^string_of_int num^", "^string_of_int denom^")"))]
                | Sexpr(Number(Float(f))) -> nl @ [(a, (i, "MAKE_LITERAL_FLOAT("^string_of_float f^")"))]
                | Sexpr(Char(c)) -> nl @ [(a, (i, "MAKE_LITERAL_CHAR("^string_of_int (Char.code c)^")"))] 
                | Sexpr(String(s)) -> 
                                    if (String.length s) = 0 
                                    then nl @ [(a, (i, "db T_STRING\n" ^
                                                       "dq ("^ labal_end_str_inc ^" - "^ labal_str_inc ^")\n" ^
                                                       labal_str_no_inc ^":\n" ^
                                                       "db \"\"\n" ^
                                                       labal_end_str_no_inc ^":\n"))]
                                    else
                                        nl @ [(a, (i,
                                                      "db T_STRING\n" ^
                                                      "dq ("^ labal_end_str_inc ^" - "^ labal_str_inc ^")\n" ^
                                                      labal_str_no_inc ^":\n" ^
                                                      "db "^ string_to_ascii_list s ^"\n" ^
                                                      labal_end_str_no_inc ^":\n"))]

                | Sexpr(Symbol(s)) -> nl @ [(a, (i, "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int (getOffSet (String(s)) nl)^")"))] 
                | Sexpr(Pair(car,cdr)) -> nl @ [a, (i, "MAKE_LITERAL_PAIR(const_tbl+"^string_of_int (getOffSet car nl)^", const_tbl+"^string_of_int (getOffSet cdr nl)^")")] 
                | _-> raise X_syntax_error)
      | a::b -> (match a with
                | Sexpr(Number(Fraction(num, denom))) -> getInternalConstsTable b (i+17) (nl @ [(a, (i, "MAKE_LITERAL_RATIONAL("^string_of_int num^", "^string_of_int denom^")"))])
                | Sexpr(Number(Float(f))) -> getInternalConstsTable b (i+9) (nl @ [(a, (i, "MAKE_LITERAL_FLOAT("^string_of_float f^")"))])
                | Sexpr(Char(c)) -> getInternalConstsTable b (i+2) (nl @ [(a, (i, "MAKE_LITERAL_CHAR("^string_of_int (Char.code c)^")"))])
                | Sexpr(String(s)) -> 
                                    if (String.length s) = 0 
                                    then getInternalConstsTable b (i+9+ (String.length s))  (nl @ [(a, (i, "db T_STRING\n" ^
                                                                                                           "dq ("^ labal_end_str_inc ^" - "^ labal_str_inc ^")\n" ^
                                                                                                           labal_str_no_inc ^":\n" ^
                                                                                                           "db \"\"\n" ^
                                                                                                           labal_end_str_no_inc ^":\n"))])
                                    else
                                        getInternalConstsTable b (i+9+ (String.length s))  (nl @ [(a, (i,
                                                                                                         "db T_STRING\n" ^
                                                                                                         "dq ("^ labal_end_str_inc ^" - "^ labal_str_inc ^")\n" ^
                                                                                                         labal_str_no_inc ^":\n" ^
                                                                                                         "db "^ string_to_ascii_list s ^"\n" ^
                                                                                                         labal_end_str_no_inc ^":\n"))])
                
                | Sexpr(Symbol(s)) -> getInternalConstsTable b (i+9) (nl @ [(a, (i, "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int (getOffSet (String(s)) nl)^")"))])
                | Sexpr(Pair(car,cdr)) -> getInternalConstsTable b (i+17) (nl @ [a, (i, "MAKE_LITERAL_PAIR(const_tbl+"^string_of_int (getOffSet car nl)^", const_tbl+"^string_of_int (getOffSet cdr nl)^")")]) 
                | _-> raise X_syntax_error)
      (* | _-> raise X_syntax_error *)
  ;;



  let rec getSubConsts c =
      match c with 
      | Sexpr(Pair(car, cdr)) -> (getSubConsts (Sexpr(car))) @ (getSubConsts (Sexpr(cdr))) @ [c]
      | Sexpr(Symbol(s)) -> [Sexpr(String(s)); c]
      | Sexpr(_) -> [c]
      | Void -> []
      (* | _-> raise X_syntax_error1 *)
  ;;

  (* deletes | Void
             | Sexpr(Nil)
             | Sexpr(Bool false)
             | Sexpr(Bool true)     from s *)
  let rec remove_initial_from_constsTable s = 
      match s with 
      | [] -> []
      | [a] -> ( match a with 
                | Void -> []
                | Sexpr(Nil) -> []
                | Sexpr(Bool false) -> []
                | Sexpr(Bool true) -> []
                | _-> [a])
      | a::b -> ( match a with 
                | Void -> remove_initial_from_constsTable b
                | Sexpr(Nil) -> remove_initial_from_constsTable b
                | Sexpr(Bool false) -> remove_initial_from_constsTable b
                | Sexpr(Bool true) -> remove_initial_from_constsTable b
                | _-> [a] @ remove_initial_from_constsTable b)
      (* | _-> raise X_syntax_error1 *)
  ;;

  let make_consts_tbl asts = 
      let constsTable_notSet = List.flatten (List.map (fun ast -> makeConstsTablePerAST ast []) asts) in
      let constsTableSet_withoutSubs = makeSet constsTable_notSet [] in
      let constsTable_withSubs = List.fold_left (fun l1 c -> l1 @ (getSubConsts c)) [] constsTableSet_withoutSubs in (* subs means sub constants *)
      let constsTableSet = makeSet constsTable_withSubs [] in
      let constsTableSet_whitoutSome = remove_initial_from_constsTable constsTableSet in
      let initial_internalConstsTable = [(Void, (0, "db T_VOID"));
                                         (Sexpr(Nil), (1, "db T_NIL"));
                                         (Sexpr(Bool false), (2, "db T_BOOL, 0"));
                                         (Sexpr(Bool true), (4, "db T_BOOL, 1"))] in
      let internalConstsTable = getInternalConstsTable constsTableSet_whitoutSome 6 initial_internalConstsTable in
      internalConstsTable
  ;;

  let rec makefVarsNameTablePerAST ast l = 
      match ast with
      | Var'(VarFree(name)) -> l @ [name]
      | Box'(VarFree(name)) -> l @ [name]
      | BoxGet'(VarFree(name)) -> l @ [name]
      | BoxSet'(VarFree(name),exp) -> makefVarsNameTablePerAST exp (l @ [name])
      | Set'(VarFree(name),exp) -> makefVarsNameTablePerAST exp (l @ [name])
      | Def'(VarFree(name),exp) -> makefVarsNameTablePerAST exp (l @ [name])
      | BoxSet'(_,exp) -> makefVarsNameTablePerAST exp l  (* cases not varFree but maybe a varfree in exp *)
      | Set'(_,exp) -> makefVarsNameTablePerAST exp l
      | Def'(_,exp) -> makefVarsNameTablePerAST exp l
      | If'(test, dit, dif) -> l @ (makefVarsNameTablePerAST test []) @ (makefVarsNameTablePerAST dit []) @ (makefVarsNameTablePerAST dif [])
      | Seq'(exps) -> List.fold_left (fun l1 l2 -> l1 @ (makefVarsNameTablePerAST l2 [])) l exps
      | Or'(exps) -> List.fold_left (fun l1 l2 -> l1 @ (makefVarsNameTablePerAST l2 [])) l exps
      | LambdaSimple'(args, body) -> makefVarsNameTablePerAST body l
      | LambdaOpt'(args, last, body) -> makefVarsNameTablePerAST body l
      | Applic'(e, exps) -> (makefVarsNameTablePerAST e []) @ (List.fold_left (fun l1 l2 -> l1 @ (makefVarsNameTablePerAST l2 [])) l exps)
      | ApplicTP'(e, exps) -> (makefVarsNameTablePerAST e []) @ (List.fold_left (fun l1 l2 -> l1 @ (makefVarsNameTablePerAST l2 [])) l exps)
      | _-> l
  ;;


  (* turns ["a"; "b"] into [("a", 0); ("b", 1)] *)
  let rec getInternalfVarsTable nameList i = match nameList with
                                            | [] -> []
                                            | [a] -> [(a, i)]
                                            | a::b -> [(a, i)] @ (getInternalfVarsTable b (i+1))
                                            (* | _-> raise X_syntax_error *)
  ;;

  

  let make_fvars_tbl asts =
    let fVarsNameTableNotSet = ["boolean?"; "flonum?"; "rational?";
                                "pair?"; "null?"; "char?"; "string?";
                                "procedure?"; "symbol?";
                                "string-length"; "string-ref"; "string-set!";
                                "make-string"; "symbol->string";
                                "char->integer"; "integer->char"; "exact->inexact";
                                "eq?";
                                "+"; "*"; "/"; "="; "<";
                                "numerator"; "denominator"; "gcd";
                                "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"] 
                                @ List.flatten (List.map (fun ast -> makefVarsNameTablePerAST ast []) asts) in
    let fVarsNameTable = makeSet fVarsNameTableNotSet [] in
    let internalfVarsTable = getInternalfVarsTable fVarsNameTable 0 in
    internalfVarsTable
  ;;


  (* unique labels *)
  (* for if and or *)
  let make_unique_Lexit = make_unique_index "Lexit" ;;
  let make_unique_Lelse = make_unique_index "Lelse" ;;
  (* for adjust_stack *)
  let make_unique_enlargeStack = make_unique_index "enlarge_stack" ;;
  let make_unique_shrinkStack = make_unique_index "shrink_stack" ;;
  let make_unique_replaceArgsEnlarge = make_unique_index "replace_args_enlarge" ;;
  let make_unique_AfterReplaceArgsEnlarge = make_unique_index "after_replace_args_enlarge" ;;
  let make_unique_replaceArgsShrink = make_unique_index "replace_args_shrink" ;;
  (* let make_unique_AfterReplaceArgsShrink = make_unique_index "after_replace_args_shrink" in *)
  let make_unique_createList = make_unique_index "create_list" ;;
  let make_unique_finishAdjust = make_unique_index "finish_adjust" ;;
  (* for lambda simple and opt *)
  let make_unique_cpyMinVec = make_unique_index "copy_minor_vectors" ;;
  let make_unique_AftercpyMinVec = make_unique_index "after_copy_minor_vectors" ;;
  let make_unique_cpyParams = make_unique_index "copy_params" ;;
  let make_unique_AftercpyParams = make_unique_index "after_copy_params" ;;
  let make_unique_Lcode = make_unique_index "Lcode" ;;
  let make_unique_Lcont = make_unique_index "Lcont" ;;
  (* for lambda opt *)
  let make_unique_adjustStuck = make_unique_index "adjust_stack_Lopt" ;;
  (* for applic *)
  let make_unique_procIsClosure = make_unique_index "proc_is_a_Closure" ;;
  (* for applicTP *)
  let make_unique_procIsClosure = make_unique_index "proc_is_a_Closure" ;;
  let make_unique_replaceFramesTP = make_unique_index "replace_frames_TP" ;;

  
  let adjust_stack args last body =
    let labal_enlargeStack_inc = make_unique_enlargeStack true in
    let labal_enlargeStack_no_inc = make_unique_enlargeStack false in

    let label_shrinkStack_inc = make_unique_shrinkStack true in
    (* let label_shrinkStack_no_inc = make_unique_shrinkStack false in *)

    let label_replaceArgsEnlarge_inc = make_unique_replaceArgsEnlarge true in
    let label_replaceArgsEnlarge_no_inc = make_unique_replaceArgsEnlarge false in

    let label_AfterReplaceArgsEnlarge_inc = make_unique_AfterReplaceArgsEnlarge true in
    let label_AfterReplaceArgsEnlarge_no_inc = make_unique_AfterReplaceArgsEnlarge false in

    let label_replaceArgsShrink_inc = make_unique_replaceArgsShrink true in
    let label_replaceArgsShrink_no_inc = make_unique_replaceArgsShrink false in

    (* let make_unique_AfterReplaceArgsShrink = make_unique_index "after_replace_args_shrink" in *)
    let label_createList_inc = make_unique_createList true in
    let label_createList_no_inc = make_unique_createList false in

    let label_finishAdjust_inc = make_unique_finishAdjust true in
    let label_finishAdjust_no_inc = make_unique_finishAdjust false in


      "mov rcx, [rsp + 2 * WORD_SIZE]\n\t\t\t" ^      (* rcx <- n *)
      "cmp rcx, "^ string_of_int (List.length args) ^"\n\t\t\t" ^
      "je "^ labal_enlargeStack_inc ^"\n\t\t\t" ^
(* shrink stack *)
      label_shrinkStack_inc ^":\n\t\t\t\t" ^
      (* creating the opt list *)
      "mov rax, SOB_NIL_ADDRESS\n\t\t\t\t" ^                               (* rax <- cdr *)
      "mov rcx, [rsp + 2 * WORD_SIZE]\n\t\t\t\t" ^                         (* rcx <- n *)
      "sub rcx, "^ string_of_int (List.length args) ^"\n\t\t\t\t" ^        (* rcx <- n - arg.length *)
      label_createList_inc ^":\n\t\t\t\t\t" ^
      "mov rbx, [rsp + (2 + "^ string_of_int (List.length args) ^" + rcx) * WORD_SIZE]\n\t\t\t\t\t" ^               (* rbx <- car *)
      "MAKE_PAIR(rdx, rbx, rax)\n\t\t\t\t\t" ^              
      "mov rax, rdx \n\t\t\t\t\t" ^                                        (* rax <- new cdr *)
      "loop "^ label_createList_no_inc ^"\n\t\t\t\t" ^
      (* putting the opt list in its place in stack*)
      "mov [rsp + (2 + 1 + "^ string_of_int (List.length args) ^") * WORD_SIZE], rax\n\t\t\t\t" ^

      (* moving all args on stack n-(args.length+1) cells in *)
      "mov rbx, [rsp + 2 * WORD_SIZE]\n\t\t\t\t" ^                           (* rbx <- n *)
      "sub rbx, "^ string_of_int (List.length args) ^" + 1\n\t\t\t\t" ^      (* rbx <- n - (args.length+1) *)
      "mov rcx, 3 + "^ string_of_int (List.length args) ^" + 1\n\t\t\t\t" ^  (* rcx <- number of cells to replace = ret,env,n + args.length + opt list *)
      label_replaceArgsShrink_inc ^":\n\t\t\t\t\t" ^
      "mov rdx, [rsp + (rcx-1) * WORD_SIZE] \n\t\t\t\t\t" ^

      "mov r8, rcx \n\t\t\t\t\t" ^
      "add r8, rbx \n\t\t\t\t\t" ^
      "dec r8\n\t\t\t\t\t" ^
      "mov [rsp + r8 * WORD_SIZE], rdx\n\t\t\t\t\t" ^
      "loop "^ label_replaceArgsShrink_no_inc ^"\n\t\t\t\t" ^

      (* changing the rsp *)
      "shl rbx, 3 \n\t\t\t\t" ^
      "add rsp, rbx \n\t\t\t\t" ^    (* to verify that rbx is the right offset to change rsp ============== *)

      (* changing n to be args.length+1 *)
      "mov qword [rsp + 2 * WORD_SIZE], "^ string_of_int ((List.length args)+1) ^"\n\t\t\t\t" ^
      (* finish shrink stack so jumping to end *)
      "jmp "^ label_finishAdjust_inc ^"\n\t\t\t" ^
      
(* enlarge stack *)
      (* inserts new_args_number to its place on stack *)
      labal_enlargeStack_no_inc ^":\n\t\t\t\t" ^
      "pop rax\n\t\t\t\t" ^   (* rax <- ret *)
      "pop rbx\n\t\t\t\t" ^   (* rbx <- env *)
      "push "^ string_of_int ((List.length args)+1) ^"\n\t\t\t\t" ^
      "push rbx\n\t\t\t\t" ^
      "push rax\n\t\t\t\t" ^

      (* moving all args on stack 1 cell out *)
      "mov rcx, 1\n\t\t\t" ^
      label_replaceArgsEnlarge_inc ^":\n\t\t\t\t" ^
      "cmp rcx, "^ string_of_int (List.length args) ^"\n\t\t\t\t" ^     (* looping for number of args (without last one) *)
      "jg "^ label_AfterReplaceArgsEnlarge_inc ^"\n\t\t\t\t" ^

      
      "mov rdx, [rsp + (3 + rcx) * WORD_SIZE]\n\t\t\t\t" ^          (* 3 to get to point on n *)
      "mov [rsp + (3 + rcx -1) * WORD_SIZE], rdx\n\t\t\t\t" ^
      "add rcx, 1\n\t\t\t\t" ^
      "jmp "^ label_replaceArgsEnlarge_no_inc ^"\n\t\t\t" ^

      label_AfterReplaceArgsEnlarge_no_inc ^":\n\t\t\t\t" ^
      (* put () in the end of the stack *)
      "mov rax, SOB_NIL_ADDRESS\n\t\t\t\t" ^
      "mov [rsp + (3 + "^ string_of_int (List.length args) ^") * WORD_SIZE], rax\n\t\t\t" ^
      (* finish enlarge stack *)
      label_finishAdjust_no_inc ^ ":\n"
  ;;


  let rec gen consts fvars e env_size = 
      match e with
      | Const'(c) -> "mov rax, const_tbl+"^ string_of_int(fst (List.assoc c consts)) ^" ;; Const'(c)\n"
      | Var'(VarFree(s)) -> "mov rax, qword [fvar_tbl+"^ string_of_int(List.assoc s fvars) ^" * 8]  ;; Var'(VarFree(s))\n"
      | Var'(VarParam(_, min)) -> 
                                  (* "mov rax, qword [rbp + 8 ∗ (4 + "^ string_of_int min ^")]\n" *)
                                  "mov rax, "^ string_of_int min ^" ;; Var'(VarParam(_, min))\n" ^
                                  "add rax, 4\n" ^
                                  "shl rax, 3\n" ^
                                  "add rax, rbp\n" ^
                                  "mov rax, qword [rax]\n"
      | Var'(VarBound(_, maj, min)) -> 
                                        (* "mov rax, qword [rbp + 8 ∗ 2]\n\t" ^ *)
                                        "mov r8, 2  ;; Var'(VarBound(_, maj, min))\n\t" ^
                                        "shl r8, 3\n\t" ^
                                        "add r8, rbp\n\t" ^
                                        "mov rax, qword [r8]\n\t" ^

                                        (* "mov rax, qword [rax + 8 ∗ "^ string_of_int maj ^"]\n\t" ^ *)
                                        "mov r8, "^ string_of_int maj ^"\n\t" ^
                                        "shl r8, 3\n\t" ^
                                        "add r8, rax\n\t" ^
                                        "mov rax, qword [r8]\n\t" ^

                                        (* "mov rax, qword [rax + 8 ∗ "^ string_of_int min ^"]\n"  *)
                                        "mov r8, "^ string_of_int min ^"\n\t" ^
                                        "shl r8, 3\n\t" ^
                                        "add r8, rax\n\t" ^
                                        "mov rax, qword [r8]\n\t"

      | Box'(v) -> gen consts fvars (Var'(v)) env_size ^
                   "\tMALLOC rbx, WORD_SIZE ;; Box'(v)\n\t" ^
                    "mov [rbx], rax\n\t" ^
                    "mov rax, rbx\n" 
      | BoxGet'(v) -> ";; BoxGet'(v)\n" ^ 
                      gen consts fvars (Var'(v)) env_size ^
                      "\tmov rax, qword [rax]\n"
      | BoxSet'(v,exp) -> ";; BoxSet'(v,exp)\n" ^
                          gen consts fvars exp env_size ^
                          "\tpush rax\n\t" ^
                           gen consts fvars (Var'(v)) env_size ^
                          "\tpop qword [rax]\n\t" ^
                           "mov rax, SOB_VOID_ADDRESS\n" 
      | If'(test, dit, dif) -> 
        let lelse_inc = make_unique_Lelse true in
        let lelse_no_inc = make_unique_Lelse false in
        let lexit_inc = make_unique_Lexit true in
        let lexit_no_inc = make_unique_Lexit false in
                                ";; If'(test, dit, dif)\n" ^
                                gen consts fvars test env_size ^
                               "\tcmp rax, SOB_FALSE_ADDRESS\n\t" ^
                               "je "^ lelse_inc ^"\n" ^   
                                gen consts fvars dit env_size ^
                               "\tjmp "^ lexit_inc ^"\n\t" ^    
                                lelse_no_inc ^":\n\t" ^ 
                                gen consts fvars dif env_size ^ "\t" ^
                                lexit_no_inc ^":\n"       

      | Seq'(exps) -> List.fold_left (fun str e -> str ^ (gen consts fvars e env_size) ^ "\n\t") "\t" exps
      | Set'(VarFree(s),exp) -> ";; Set'(VarFree(s),exp)\n" ^
                                (gen consts fvars exp env_size) ^
                                "\tmov qword [fvar_tbl+"^ string_of_int(List.assoc s fvars) ^" * 8], rax\n\t" ^
                                 "mov rax, SOB_VOID_ADDRESS\n" 
      | Set'(VarParam(_, min),exp) -> ";; Set'(VarParam(_, min),exp)\n" ^
                                (gen consts fvars exp env_size) ^
                                (* "\tmov qword [rbp + 8 ∗ (4 + "^string_of_int min^")], rax\n\t" ^ *)
                                "\tmov r8, "^string_of_int min^"\n\t" ^
                                "\tadd r8, 4\n\t" ^
                                "\tshl r8, 3\n\t" ^
                                "\tadd r8, rbp\n\t" ^
                                "\tmov qword [r8], rax\n\t" ^

                                 "mov rax, SOB_VOID_ADDRESS\n"
      | Set'(VarBound(_, maj, min),exp) -> ";; Set'(VarBound(_, maj, min),exp)\n" ^
                                (gen consts fvars exp env_size) ^
                                "\tmov rbx, qword [rbp + 8 ∗ 2]\n\t" ^
                                 "mov rbx, qword [rbx + 8 ∗ "^string_of_int maj^"]\n\t" ^
                                 "mov qword [rbx + 8 ∗ "^string_of_int min^"], rax\n\t" ^
                                 "mov rax, SOB_VOID_ADDRESS\n"
      | Def'(VarFree(s),exp) -> ";; Def'(VarFree(s),exp)\n" ^
                       gen consts fvars exp env_size ^
                       "\tmov qword [fvar_tbl+"^ string_of_int(List.assoc s fvars) ^ " * WORD_SIZE], rax\n\t" ^
                       "mov rax, SOB_VOID_ADDRESS\n"
      | Or'(exps) -> 
          let lexit_inc = make_unique_Lexit true in
          let lexit_no_inc = make_unique_Lexit false in

          let exps_withoutFirstLast = List.tl (List.rev (List.tl (List.rev exps))) in
          let first = List.hd exps in
          let last = List.hd(List.rev exps) in
                                              (gen consts fvars first env_size) ^     (* gen 1st exp *)
                                              "\tcmp rax, SOB_FALSE_ADDRESS\n\t" ^
                                              "jne "^ lexit_inc ^"\n\t" ^
          (List.fold_left (fun str e -> str ^ (gen consts fvars e env_size) ^         (* gen middle exps *)
                                              "cmp rax, SOB_FALSE_ADDRESS\n" ^
                                              "jne "^ lexit_no_inc ^"\n\t") "" exps_withoutFirstLast) ^
                                              (gen consts fvars last env_size) ^      (* gen last exp *)
                                              "\t" ^ lexit_no_inc ^":\n"      

      | LambdaSimple'(args, body) -> 
          let label_cpyMinVec_inc = make_unique_cpyMinVec true in
          let label_cpyMinVec_no_inc = make_unique_cpyMinVec false in

          let label_AftercpyMinVec_inc = make_unique_AftercpyMinVec true in
          let label_AftercpyMinVec_no_inc = make_unique_AftercpyMinVec false in

          let label_cpyParams_inc = make_unique_cpyParams true in
          let label_cpyParams_no_inc = make_unique_cpyParams false in

          let label_AftercpyParams_inc = make_unique_AftercpyParams true in
          let label_AftercpyParams_no_inc = make_unique_AftercpyParams false in

          let label_Lcode_inc = make_unique_Lcode true in
          let label_Lcode_no_inc = make_unique_Lcode false in

          let label_Lcont_inc = make_unique_Lcont true in
          let label_Lcont_no_inc = make_unique_Lcont false in

              "MALLOC rax, WORD_SIZE * "^ string_of_int (1+ env_size) ^" ;; allocates mem for extEnv, rax <- pointer to extEnv \n\t" ^
              "mov rbx, [rbp + 2 * WORD_SIZE]        ;; rbx <- pointer to the array of all envs \n\t" ^
              "mov rcx, "^ string_of_int env_size ^" ;; rcx <- size of env \n\t" ^
              "cmp rcx, 0\n\t" ^
              "jle "^ label_AftercpyMinVec_inc ^"\n\t" ^

              label_cpyMinVec_inc ^":                ;; copying the pointers minor vectors from env to extEnv \n\t\t" ^
              "mov rdx, [rbx + (rcx-1) * WORD_SIZE]\n\t\t" ^
              "mov [rax + rcx * WORD_SIZE], rdx\n\t\t" ^
              "loop "^ label_cpyMinVec_no_inc ^"\n\t" ^

              label_AftercpyMinVec_no_inc ^":\n\t" ^
              "\tmov rcx, [rbp + 3 * WORD_SIZE]     ;; rcx <- number of params \n\t" ^
              (* "\tmov rcx, [rsp]                     ;; rcx <- number of params (this is the last thing on stack after applic pushes this) \n\t" ^ *)
              "mov r8, SOB_NIL_ADDRESS              ;; in case there are no params \n\t" ^
              "cmp rcx, 0\n\t" ^
              "jle "^ label_AftercpyParams_inc ^"\n\t" ^    
              "\tmov r9, rcx                        ;; r9 <- rcx \n\t" ^
              "\tshl r9, 3                         ;; r9 is multiplied by WORD_SIZE \n\t" ^
              "MALLOC r8, r9                       ;; allocates mem for extEnv[0], r8 <- pointer to extEnv[0] \n\t" ^

              label_cpyParams_inc ^":               ;; copying the params from env to extEnv[0] \n\t\t" ^
              "mov rdx, [rbp + (3+rcx) * WORD_SIZE]\n\t\t" ^
              (* "mov rdx, [rsp + rcx * WORD_SIZE]\n\t\t" ^ *)
              "mov [r8 + (rcx-1) * WORD_SIZE], rdx\n\t\t" ^
              "loop "^ label_cpyParams_no_inc ^"\n\t" ^

              label_AftercpyParams_no_inc ^":\n\t" ^
              "\tmov [rax + 0 * WORD_SIZE], r8      ;; put pointer to extEnv[0] in dedicated address, rax now holds the pointer to full extEnv \n\t" ^
              "mov rbx, rax                         ;; rbx <- rax \n\t" ^
              "MAKE_CLOSURE(rax, rbx, "^ label_Lcode_inc ^")\n\t" ^
              "jmp "^ label_Lcont_inc ^"\n\t" ^ 

              label_Lcode_no_inc ^":                ;; Lcode for the closure \n\t\t" ^
              "push rbp\n\t\t" ^
              "mov rbp, rsp\n\t\t" ^
              gen consts fvars body (env_size+1) ^
              "\t\tleave\n\t\t" ^
              "ret\n\t" ^

              label_Lcont_no_inc ^":\n"

      | LambdaOpt'(args, last, body) -> 
          let label_cpyMinVec_inc = make_unique_cpyMinVec true in
          let label_cpyMinVec_no_inc = make_unique_cpyMinVec false in

          let label_AftercpyMinVec_inc = make_unique_AftercpyMinVec true in
          let label_AftercpyMinVec_no_inc = make_unique_AftercpyMinVec false in

          let label_cpyParams_inc = make_unique_cpyParams true in
          let label_cpyParams_no_inc = make_unique_cpyParams false in

          let label_AftercpyParams_inc = make_unique_AftercpyParams true in
          let label_AftercpyParams_no_inc = make_unique_AftercpyParams false in

          let label_Lcode_inc = make_unique_Lcode true in
          let label_Lcode_no_inc = make_unique_Lcode false in

          let label_Lcont_inc = make_unique_Lcont true in
          let label_Lcont_no_inc = make_unique_Lcont false in

          let label_adjustStuck_inc = make_unique_adjustStuck true in
      
              "MALLOC rax, WORD_SIZE * "^ string_of_int (1+ env_size) ^"\n\t" ^ (* allocates mem for extEnv *)
              "mov rbx, [rbp + 2 * WORD_SIZE]\n\t" ^
              "mov rcx, "^ string_of_int env_size ^"\n\t" ^ (* rcx <- size of env *)
              "cmp rcx, 0\n\t" ^
              "jle "^ label_AftercpyMinVec_inc ^"\n\t" ^

              label_cpyMinVec_inc ^":\n\t\t" ^         (* copying the pointers minor vectors from env to extEnv *)
              "mov rdx, [rbx + (rcx-1) * WORD_SIZE]\n\t\t" ^
              "mov [rax + rcx * WORD_SIZE], rdx\n\t\t" ^
              "loop "^ label_cpyMinVec_no_inc ^"\n\t" ^

              label_AftercpyMinVec_no_inc ^":\n\t" ^
              "\tmov rcx, [rbp + 3 * WORD_SIZE]\n\t" ^      (* rcx <- number of params *)
              "mov r8, SOB_NIL_ADDRESS\n\t" ^              (* in case there are no params *)
              "cmp rcx, 0\n\t" ^
              "jle "^ label_AftercpyParams_inc ^"\n\t" ^
              "\tmov r9, rcx                        ;; r9 <- rcx \n\t" ^
              "\tshl r9, 3                         ;; r9 is multiplied by WORD_SIZE \n\t" ^
              "MALLOC r8, r9                       ;; allocates mem for extEnv[0], r8 <- pointer to extEnv[0] \n\t" ^

              label_cpyParams_inc ^":\n\t\t" ^         (* copying the params from env to extEnv[0] *)
              "mov rdx, [rbp + (3+rcx) * WORD_SIZE]\n\t\t" ^
              "mov [r8 + (rcx-1) * WORD_SIZE], rdx\n\t\t" ^
              "loop "^ label_cpyParams_no_inc ^"\n\t" ^

              label_AftercpyParams_no_inc ^":\n\t" ^
              "\tmov [rax + 0 * WORD_SIZE], r8\n\t" ^      (* put pointer to extEnv[0] in dedicated address, rax now holds the pointer to full extEnv *)
              "mov rbx, rax\n\t" ^                          (* rbx <- rax *)
              "MAKE_CLOSURE(rax, rbx, "^ label_Lcode_inc ^")\n\t" ^
              "jmp "^ label_Lcont_inc ^"\n\t" ^ 

              (* Lcode for the closure *)
              label_Lcode_no_inc ^":\n\t\t" ^
              label_adjustStuck_inc ^":\n\t\t" ^
              adjust_stack args last body ^           
              "\t\tpush rbp\n\t\t" ^
              "mov rbp, rsp\n\t\t" ^
              gen consts fvars body (env_size+1) ^
              "\t\tleave\n\t\t" ^
              "ret\n\t" ^
              label_Lcont_no_inc ^":\n"


      | Applic'(proc, exps) ->
        let label_procIsClosure_inc = make_unique_procIsClosure true in
        let label_procIsClosure_no_inc = make_unique_procIsClosure false in
                            ";; Applic'(proc, exps)\n" ^
                            (List.fold_right (fun ex str -> str ^ 
                                                          (gen consts fvars ex env_size) ^"\n" ^
                                                          "push rax\n") exps "") ^
                            "push "^ string_of_int (List.length exps) ^"\n\t" ^     (* pushing n *)
                            (gen consts fvars proc env_size) ^
                            (* Verify that rax has type closure *)
                            "\tcmp byte [rax], T_CLOSURE\n\t" ^
                            "je "^ label_procIsClosure_inc ^"\n\t" ^
                            (* case rax doesn't have type closure *)
                            (* handle exception============================ *)
                            "mov rax, 0\n\t" ^
                            "leave\n\t" ^
                            "ret\n\t" ^
                            (* case rax has type closure *)
                            label_procIsClosure_no_inc ^ ":\n\t\t" ^
                            (* pushing env *)
                            "push qword [rax + TYPE_SIZE]\n\t\t" ^           
                            (* calling code *)
                            "call qword [rax + TYPE_SIZE + WORD_SIZE]\n\t\t" ^       (* jumping to proc_code section *)

                            (* upon returning from proc 
                             poping env, n, and the n arguments from the stack *)
                            "add rsp , 8*1     ; pop env\n\t\t" ^
                            "pop rbx           ; pop arg count\n\t\t" ^
                            "shl rbx , 3       ; rbx = rbx * 8\n\t\t" ^
                            "add rsp , rbx     ; pop args\n"   

      | ApplicTP'(proc, exps) -> 
        let label_procIsClosure_inc = make_unique_procIsClosure true in
        let label_procIsClosure_no_inc = make_unique_procIsClosure false in

        let label_replaceFramesTP_inc = make_unique_replaceFramesTP true in
        let label_replaceFramesTP_no_inc = make_unique_replaceFramesTP false in


                            ";; ApplicTP'(proc, exps)\n" ^
                            (List.fold_right (fun ex str -> str ^ 
                                                          (gen consts fvars ex env_size) ^"\n\t" ^
                                                          "push rax\n\t") exps "\t") ^
                            "\tpush "^ string_of_int (List.length exps) ^"\n\t" ^   (* pushing n *)
                            (gen consts fvars proc env_size) ^

                            (* Verify that rax has type closure *)
                            "cmp byte [rax], T_CLOSURE\n\t" ^
                            "je "^ label_procIsClosure_inc ^"\n\t" ^
                            (* case rax doesn't have type closure *)
                            (* handle exception============================ *)
                            "mov rax, 0\n\t" ^
                            "leave\n\t" ^
                            "ret\n\t" ^
                            


                            (* case rax has type closure *)
                            label_procIsClosure_no_inc ^ ":\n\t" ^
                            (* pushing env *)
                            "push qword [rax + TYPE_SIZE]\n\t" ^   
                            "push qword [rbp + 8 * 1]       ; old ret addr\n\t" ^

          (* fixing stack *)
                            "mov rcx, [rsp + 2 * WORD_SIZE]\n\t" ^        (* rcx <- m ( = number of new_args) *)
                            "add rcx, 3\n\t" ^                            (* rcx <- newFrame size = m + 3 ( = m,env,ret) *)
                            "mov rdx, [rbp + 3 * WORD_SIZE]\n\t" ^        (* rdx <- n ( = number of old_args) *)
                            "add rdx, 4\n\t" ^                            (* rdx <- oldFrame size = n + 4 ( = n,env,ret,rbp) *)
                            "mov r8, rdx\n\t" ^                           (* r8  <- oldFrame size (saved for a future purpose) *)
                            "mov r9, [rbp]\n\t" ^                         (* r9  <- old_rbp (saved for a future purpose) *)

                            (* replacing oldFrame with newFrame *)
                            label_replaceFramesTP_inc ^ ":\n\t\t" ^
                            (* r10 will hold new_arg's place -> rsp + (rcx-1) * WORD_SIZE   *)           
                            "mov r10, rcx\n\t\t" ^                            (* r10 <- (rcx) *)
                            "dec r10\n\t\t" ^                                 (* r10 <- (rcx-1) *)
                            "shl r10, 3\n\t\t" ^                              (* r10 <- (rcx-1) * WORD_SIZE   *)
                            "add r10, rsp\n\t\t" ^                            (* r10 <- rsp + (rcx-1) * WORD_SIZE   *)
                            "mov rbx, [r10]\n\t\t" ^                          (* rbx <- new_arg *)

                            (* r10 will hold old_arg's place -> rbp + (rdx-1) * WORD_SIZE   *)           
                            "mov r10, rdx\n\t\t" ^                            (* r10 <- (rdx) *)
                            "dec r10\n\t\t" ^                                 (* r10 <- (rdx-1) *)
                            "shl r10, 3\n\t\t" ^                              (* r10 <- (rdx-1) * WORD_SIZE   *)
                            "add r10, rbp\n\t\t" ^                            (* r10 <- rbp + (rdx-1) * WORD_SIZE   *)
                            "mov [r10], rbx\n\t\t" ^                          (* put rbx in old_arg's place *)

                            "dec rdx\n\t\t" ^
                            "loop "^ label_replaceFramesTP_no_inc ^"\n\t" ^

                            (* change the rsp according to the number of cells deleted *)
                            "shl r8, 3\n\t" ^
                            "add rsp, r8\n\t" ^
                            (* change the rbp to point to the frame before the TP_frame  *)
                            "mov rbp, r9\n\t" ^
          (* finish fixing stack *)
                            (* jumping to the code (instead of call) *)
                            "jmp [rax + TYPE_SIZE + WORD_SIZE]\n\t"      (* jump to proc_code section *)

      | _-> raise X_this_should_not_happen
  ;;

  let generate consts fvars e = gen consts fvars e 0 ;;

end;;

