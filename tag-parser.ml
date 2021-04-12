
#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_syntax_error1;;


module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* ----------------------------------------------------------help functions-------------------------------------------------------- *)

let rec lastElement list =  (* returns last element of l a list *)
    match list with
      | [] -> ""
      | [x] -> x
      | _ :: t -> lastElement t;;

let rec pair_to_list p = 
    match p with
      | Nil -> []
      | Symbol(_) -> [p]
      | Pair(a,b) -> a :: pair_to_list b 
      | _-> raise X_syntax_error1

let rec  no_nested_begin exps = match exps with
                                | Pair(Pair(Symbol "begin", restExp), Nil) -> no_nested_begin restExp
                                | Pair(a, b) -> Pair(a, no_nested_begin b)
                                | exp -> exp;;

(* ------------------------------------------------------------------------------------------------------------------ *)

let rec tag_parse sexpr =  
  match sexpr with
  | Bool _ | Char _ | Number _ | String _ -> Const(Sexpr(sexpr))
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("define"), Pair(Symbol(name), Pair(exp, Nil))) -> Def(tag_parse (Symbol(name)), tag_parse exp)
  | Pair(Symbol("set!"), Pair(Symbol(name), Pair(exp, Nil))) -> Set(tag_parse (Symbol(name)), tag_parse exp) 
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
          If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) ->
          If(tag_parse test, tag_parse dit, Const(Void))
  | Pair(Symbol("or"), orExps) ->  
        (match orExps with
        | Nil -> tag_parse (Bool(false))
        | Pair(a,b) -> Or(List.map tag_parse (pair_to_list orExps))
        | _-> raise X_syntax_error)
  | Pair(Symbol("lambda"), Pair(args, body)) -> parse_lambda args body      (* "(lambda (a b) (+ a b) (- a b))" *) 
(* ----------------------------------------------------------explicitSequences parser-------------------------------------------------------- *)
  | Pair(Symbol "begin", exps) -> 
        if exps = Nil then Const(Void)
        else
            let exps1 = no_nested_begin exps in
            parse_sequence exps1
    
(* ----------------------------------------------------------macros parser-------------------------------------------------------- *)

  | Pair(Symbol("quasiquote"), Pair(exp, Nil)) -> parseQuasiquote exp
  | Pair(Symbol "cond", ribs) -> tag_parse (parseCond ribs)
  | Pair(Symbol("and"), andExps) -> tag_parse (parseAnd andExps) 
  | Pair(Symbol("let"), Pair(bindings, body)) -> tag_parse (parse_let bindings body)  (* (let ((a 1) (b 2)) (f a) (f b)) ==> *)
                                                                                                 (* ((lambda (a b) (+ a b) (f a b)) 1 2) *)
  | Pair(Symbol("let*"), Pair(bindings, body)) -> tag_parse (parse_let_star bindings body)
  | Pair(Symbol("letrec"), Pair(bindings, body)) -> tag_parse (parse_let_rec bindings body)
  | Pair(Symbol("define"), Pair(Pair(Symbol(varName), argList), body)) -> tag_parse (parse_mit_define varName argList body)
  | Pair(Symbol "pset!", body) -> tag_parse (parse_Pset body)

(* ----------------------------------------------------------application parser-------------------------------------------------------- *)
  | Pair(funcExp, params) ->   Applic(tag_parse funcExp, List.map tag_parse (pair_to_list params)) 
      (* (func 1 2) *)

  | Symbol(x) -> if (List.mem x reserved_word_list)
                 then raise X_syntax_error
                 else Var(x)

  | _ -> raise X_syntax_error
(* ----------------------------------------------------------start macro functions-------------------------------------------------------- *)

and parseQuasiquote exp =
    match exp with
    | Pair(Symbol("unquote"), Pair(x, Nil)) -> tag_parse x
    | Pair(Symbol("unquote-splicing"), Pair(x, Nil)) -> tag_parse (Pair(Symbol("quote"), Pair(Pair(Symbol("unquote-splicing"), Pair(x, Nil)), Nil)))
    | Nil | Symbol _ ->  tag_parse (Pair(Symbol("quote"), Pair(exp, Nil)))
    (* case 4 wat , probably not required*)
    | Pair(Pair(Symbol("unquote-splicing"), Pair(x, Nil)), b) -> Applic(Var("append"), [tag_parse x; tag_parse (Pair(Symbol("quasiquote"), Pair(b, Nil)))]) 
    | Pair(a, Pair(Symbol("unquote-splicing"), Pair(x, Nil))) -> Applic(Var("cons"), [tag_parse (Pair(Symbol("quasiquote"), Pair(a, Nil))); tag_parse x]) 
    | Pair(a, b) -> Applic(Var("cons"), [tag_parse (Pair(Symbol("quasiquote"), Pair(a, Nil))); tag_parse (Pair(Symbol("quasiquote"), Pair(b, Nil)))]) 
    | Bool _ | Char _ | Number _ | String _ -> tag_parse exp

and parseCond ribs =
     match ribs with   
   (* Pair(rib, restRibs) *) 
    | Pair(Pair(test, Pair(Symbol("=>"), Pair(body, Nil))), Nil) ->  (* case 2 *)
                                                                  if body = Nil then raise X_syntax_error 
                                                                  else
                                                                      Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(test, Nil)), 
                                                                                                    Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(body, Nil))), Nil)), 
                                                                                                          Nil)), 
                                                                                              Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil)))
    | Pair(Pair(test, Pair(Symbol("=>"), Pair(body, Nil))), restRibs) ->  (* case 2 *)
                                                                  if body = Nil then raise X_syntax_error 
                                                                  else
                                                                      Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(test, Nil)), 
                                                                                                    Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(body, Nil))), Nil)), 
                                                                                                          Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(parseCond restRibs, Nil))), Nil)), Nil))), 
                                                                                              Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)))    
    | Pair(Pair(Symbol("else"), body), restRibs) ->  (* case 3 *)
                                            if body = Nil then raise X_syntax_error 
                                            else
                                                Pair(Symbol("begin"), body)
    | Pair(Pair(test, body), Nil) ->  (* case 1 *)
                                   if body = Nil then raise X_syntax_error 
                                   else
                                       Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), body), Nil)))
    | Pair(Pair(test, body), restRibs) ->  (* case 1 *)
                                   if body = Nil then raise X_syntax_error 
                                   else
                                       Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), body), Pair(parseCond restRibs, Nil))))
    | _ -> raise X_syntax_error                                                         
(* ----------------------------------------------------------calculations case 2-------------------------------------------------------- *)
(* (let a b) ---> Pair(Symbol("let"), Pair(a, Pair(b, Nil)))
a = Pair(a1, Pair(a2, Pair(a3, Nil)))
b = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Symbol("f"), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil))))
a1 = Pair(Symbol("value"), Pair(test, Nil))
a2 = Pair(Symbol("f"), Pair(Pair(Symbol("Lambda"), Pair(argList1, Pair(body, Nil))), Nil))
a3 = Pair(Symbol("rest"), Pair(Pair(Symbol("Lambda"), Pair(argList2, Pair(parseCond restRibs, Nil))), Nil))
a = Pair(a1, 
         Pair(a2, 
              Pair(a3, Nil)))
Pair(Symbol("let"), Pair(a, 
                         Pair(b, Nil)))
(let ((value ⟨test⟩)
        (f (lambda () ⟨exprf⟩))
        (rest (lambda () ⟨continue with cond-ribs⟩)))
        (if value
            (f value)
            (rest))) *)
(* ----------------------------------------------------------end calculations-------------------------------------------------------- *)

and parse_let bindings body = 
  if body = Nil then raise X_syntax_error 
  else
        Pair(Pair(Symbol("lambda"), Pair(get_args bindings, body)), get_vals bindings)

and get_args bindings =
    match bindings with
    | Nil -> Nil
    | Pair(Pair(arg, Pair(value, Nil)), restBinds) -> Pair(arg, get_args restBinds)
    | _ -> raise X_syntax_error

(* letrec problem here: *)

and get_vals bindings =
    match bindings with
    | Nil -> Nil
    | Pair(Pair(arg, Pair(value, Nil)), restBinds) -> Pair(value, get_vals restBinds)
    | _ -> raise X_syntax_error

and parse_let_star bindings body =
  if body = Nil then raise X_syntax_error 
  else
    match bindings with
    | Nil -> Pair(Symbol("let"), Pair(bindings, body))
    | Pair(single, Nil) -> Pair(Symbol("let"), Pair(Pair(single, Nil), body))
    | Pair(first, restBinds) -> Pair(Symbol("let"), Pair(Pair(first, Nil), Pair(parse_let_star restBinds body, Nil)))
    | _-> raise X_syntax_error

and parse_let_rec bindings body = 
  if body = Nil then raise X_syntax_error
  else
    match bindings with
    | Pair(Pair(Symbol(argName), Pair(exp, Nil)), rest) -> Pair(Symbol("let"), Pair(parse_let_rec_bindings bindings, parse_let_rec_body bindings body))
    | _ -> raise X_syntax_error

and parse_let_rec_bindings bindings = 
    match bindings with
    | Nil -> Nil
    | Pair(Pair(Symbol(argName), Pair(exp, Nil)), rest) -> Pair(Pair(Symbol(argName), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), parse_let_rec_bindings rest)
    | _ -> raise X_syntax_error

and parse_let_rec_body bindings body = 
    match bindings with
    | Nil -> body  
    (* Pair(Pair(Symbol("let"), Pair(Nil,body)), Nil)  /  Pair(Symbol("let"), Pair(Nil, body))  /  Pair(Pair(Symbol("let"), Pair(Nil,body)), Nil)  is last exp "let" really needed in letrec? *)
    | Pair(Pair(Symbol(argName), Pair(exp, Nil)), rest) -> Pair(Pair(Symbol("set!"), Pair(Symbol(argName), Pair(exp, Nil))), parse_let_rec_body rest body)
    | _ -> raise X_syntax_error

and parseAnd exps =
    match exps with
    | Nil -> Bool(true)
    | Pair(single, Nil) -> single
    | Pair(first, rest) -> Pair(Symbol("if"), Pair(first, Pair((parseAnd rest), Pair(Bool(false), Nil))))
    | _ -> raise X_syntax_error

and parse_mit_define varName argList body = 
    match body with
    | Nil -> raise X_syntax_error
    | _ -> Pair(Symbol("define"), Pair(Symbol(varName), Pair(Pair(Symbol("lambda"), Pair(argList, body)), Nil)))

and parse_Pset body = 
  if body = Nil then raise X_syntax_error 
  else
    match body with
    | Pair(single, Nil) -> Pair(Symbol("set!"), single)
    | Pair(Pair(Symbol(vi), Pair(expri, Nil)), restBinds) -> 

          Pair(Symbol("let"), Pair(Pair(Pair(Symbol("temp1"), Pair(expri, Nil)), 
                                        Pair(Pair(Symbol("temp2"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(parse_Pset restBinds, Nil))), Nil)), 
                                            Pair(Pair(Symbol("temp3"), Pair(Pair(Symbol("lambda"), Pair(Pair(Symbol("t"), Nil), Pair(Pair(Symbol("set!"), Pair(Symbol(vi), Pair(Symbol("t"), Nil))), Nil))), Nil)), Nil))), 
                                  Pair(Pair(Symbol("temp2"), Nil), Pair(Pair(Symbol("temp3"), Pair(Symbol("temp1"), Nil)), Nil)))) 
    | _ -> raise X_syntax_error

(* ----------------------------------------------------------calculations Pset!-------------------------------------------------------- *)
(* (let ((temp1 expri)
         (temp2 (lambda () (parse_Pset restBinds)))
         (temp3 (lambda (t) (set! vi t)))
            )
        (temp2)
        (temp3 temp1)
    )                                     *)

(* (let a b) ---> Pair(Symbol("let"), Pair(a, Pair(b, Nil)))
a = Pair(a1, 
         Pair(a2, 
              Pair(a3, Nil)))

b = Pair(b1, Pair(b2, Nil))            
Pair(Symbol("let"), Pair(Pair(a1, 
                              Pair(a2, 
                                   Pair(a3, Nil))), 
                         Pair(b1, Pair(b2, Nil))))      *)

(* a1 = Pair(Symbol("temp1"), Pair(expri, Nil))
a2 = Pair(Symbol("temp2"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(parse_Pset restBinds, Nil), Nil))), Nil))
a3 = Pair(Symbol("temp3"), Pair(Pair(Symbol("lambda"), Pair(Pair(Symbol(t), Nil), Pair(Pair(Symbol("set!"), Pair(Symbol(vi), Pair(Symbol(t), Nil))), Nil))), Nil))
b1 = Pair(Symbol("temp2"), Nil)
b2 = Pair(Symbol("temp3"), Pair(Symbol("temp1"), Nil))

Pair(Symbol("let"), Pair(Pair(Pair(Symbol("temp1"), Pair(expri, Nil)), 
                              Pair(Pair(Symbol("temp2"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(parse_Pset restBinds, Nil), Nil))), Nil)), 
                                   Pair(Pair(Symbol("temp3"), Pair(Pair(Symbol("lambda"), Pair(Pair(Symbol(t), Nil), Pair(Pair(Symbol("set!"), Pair(Symbol(vi), Pair(Symbol(t), Nil))), Nil))), Nil)), Nil))), 
                         Pair(Pair(Symbol("temp2"), Nil), Pair(Pair(Symbol("temp3"), Pair(Symbol("temp1"), Nil)), Nil))))  *)
(* ----------------------------------------------------------end calculations-------------------------------------------------------- *)
(* ----------------------------------------------------------end macro functions-------------------------------------------------------- *)
(* ----------------------------------------------------------lambda parser-------------------------------------------------------- *)
and parse_lambda args body = 
    
    let names = argsNames args in
    if (List.exists (fun s-> (List.exists (fun r-> r=s ) reserved_word_list) ) names) 
    then raise X_syntax_error
    else
        if isSimple args (* args.last=Nil || arg=Nil *)
        then  (* case lambdaSimple *)
            (match body with 
            | Nil -> raise X_syntax_error
            | Pair(bodyExp, Nil) ->  LambdaSimple(names, tag_parse bodyExp)
            | _-> LambdaSimple(names, parse_sequence body) ) 

        else (* case LambdaOpt *)
            (match args with 
            | Symbol(name) -> if List.mem name reserved_word_list
                                  then raise X_syntax_error
                                  else (match body with 
                                       | Nil -> raise X_syntax_error1
                                       | Pair(bodyExp, Nil) -> LambdaOpt([], name, tag_parse bodyExp)
                                       | _-> LambdaOpt([], name, parse_sequence body)    (*case variadic*) )
                                  
            | Pair(a, b) ->  
                      let lastArg = lastElement names in 
                      let reversedList = (List.rev names) in
                      let tailedList = (List.tl reversedList) in
                      let shortedList = (List.rev tailedList) in (* = argsNames without last element *)
                      (match body with 
                      | Nil -> raise X_syntax_error
                      | Pair(bodyExp, Nil) -> LambdaOpt(shortedList, lastArg, tag_parse bodyExp)
                      | _-> LambdaOpt(shortedList, lastArg, parse_sequence body) )
            | _ -> raise X_syntax_error )

and parse_sequence exps = 
      (match exps with
      | Nil -> Const(Void)
      | Pair(single, Nil) -> tag_parse single
      | Pair(a,b) -> Seq(List.map tag_parse (pair_to_list exps))    (* case list of element *)
      | _-> raise X_syntax_error1)

and argsNames args = 
    match args with 
    | Symbol(name) -> [name] 
    | _-> List.map (fun arg-> (match arg with 
                        | Symbol(name) -> name 
                        | _-> raise X_syntax_error1)) 
             (pair_to_list args)
    

and isSimple args =
    match args with 
    | Nil -> true 
    | Pair(Symbol _, Symbol _) -> false
    | Pair(Symbol _, rest) -> isSimple rest
    | Symbol(_) -> false  (* args is not a list but a var *)
    | _ -> raise X_syntax_error1
    ;;

let tag_parse_expressions sexprList = List.map tag_parse sexprList ;;


end;;(*  struct Tag_Parser *)

