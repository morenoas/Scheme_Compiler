
#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;
exception X_syntax_error1;;
exception X_syntax_error2;;


module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec annotate_lexical_addresses e =  
    match e with
    | Const(c) -> Const'(c)
    | Var(varName) -> Var'(VarFree(varName))
    | If(test, dit, dif) -> If'(annotate_lexical_addresses test, annotate_lexical_addresses dit, annotate_lexical_addresses dif)
    | Seq(l) -> Seq'(List.map annotate_lexical_addresses l)
    | Set(v, exp) -> 
               let var = annotate_lexical_addresses v in
                (match var with
                | Var'(x) -> Set'(x, annotate_lexical_addresses exp)
                | _-> raise X_syntax_error)
    | Def(v, exp) -> 
                let var = annotate_lexical_addresses v in
                (match var with
                | Var'(x) -> Def'(x, annotate_lexical_addresses exp)
                | _-> raise X_syntax_error)
    
    | Or(l) -> Or'(List.map annotate_lexical_addresses l)
    | LambdaSimple(args, body) -> LambdaSimple'(args, annotate_lexical_addresses_lambda [args] body)
    | LambdaOpt(args, last, body) -> LambdaOpt'(args, last, annotate_lexical_addresses_lambda [List.append args [last]] body)
    | Applic(e, exps) -> Applic'(annotate_lexical_addresses e, List.map annotate_lexical_addresses exps)
    (* | _-> raise X_syntax_error *)
(* ----------------------------------------------------------lexical_addresses lambda-------------------------------------------------------- *)
(* args: [args1, args2, ...] *)
and annotate_lexical_addresses_lambda args body =
    match body with
    | Const(c) -> Const'(c)
    | Var(varName) ->  
        let (major, minor) = get_major_minor varName args in
        (match (major, minor) with
        | (-1, _) -> Var'(VarFree(varName))
        | (0, _) -> Var'(VarParam(varName, minor))
        | _-> Var'(VarBound(varName, major-1, minor)) 
        )
    | If(test, dit, dif) -> If'(annotate_lexical_addresses_lambda args test, annotate_lexical_addresses_lambda args dit, annotate_lexical_addresses_lambda args dif)
    | Seq(l) -> Seq'(List.map (fun e-> annotate_lexical_addresses_lambda args e) l)
    | Set(v, exp) -> 
               let var = annotate_lexical_addresses_lambda args v in
                (match var with
                | Var'(x) -> Set'(x, annotate_lexical_addresses_lambda args exp)
                | _-> raise X_syntax_error)
    | Def(v, exp) -> 
                let var = annotate_lexical_addresses_lambda args v in
                (match var with
                | Var'(x) -> Def'(x, annotate_lexical_addresses_lambda args exp)
                | _-> raise X_syntax_error)
    | Or(l) -> Or'(List.map (fun e-> annotate_lexical_addresses_lambda args e) l)
    | LambdaSimple(args1, body1) -> LambdaSimple'(args1, annotate_lexical_addresses_lambda (List.append [args1] args) body1)
    | LambdaOpt(args1, last1, body1) -> LambdaOpt'(args1, last1, annotate_lexical_addresses_lambda (List.append [List.append args1 [last1]] args) body1)
    | Applic(e, exps) -> Applic'(annotate_lexical_addresses_lambda args e, List.map (fun e-> annotate_lexical_addresses_lambda args e) exps)
    (* | _-> raise X_syntax_error *)


and get_minor e l = (* returns e's index in l *)
    if e = List.nth l 0
    then 0
    else 1 + get_minor e (List.tl l)

and get_major e lol = (* returns e's list index in lol. returns lol.length if e isn't there *)
    if lol != []
    then if List.mem e (List.nth lol 0)
         then 0
         else 1 + get_major e (List.tl lol)
    else 0
    
(* lol means list of lists 
   returns (e's list index in lol, minor) *)
and get_major_minor e lol = 
    let major = get_major e lol in 
    if major = List.length lol
    then (-1, -1)
    else (major, get_minor e (List.nth lol major))
    
;;

let rec tp_calls e in_tp =
    match e with
    | Const'(_) | Var'(_) -> e
    | If'(test, dit, dif) -> If'(tp_calls test false, tp_calls dit in_tp, tp_calls dif in_tp)
    | Seq'(l) -> 
           let shortedList = List.rev (List.tl (List.rev l)) in
           let last = lastOf l in
           Seq'(List.append (List.map (fun e-> tp_calls e false) shortedList) [tp_calls last in_tp])
    | Set'(v, exp) -> Set'(v, tp_calls exp false)
    | Def'(v, exp) -> Def'(v, tp_calls exp false)
    | Or'(exps) -> 
    (* exps can't be [] due to tag-parser *)
           let shortedList = List.rev (List.tl (List.rev exps)) in
           let last = lastOf exps in
           Or'(List.append (List.map (fun e-> tp_calls e false) shortedList) [tp_calls last in_tp])
    | LambdaSimple'(args, body) -> LambdaSimple'(args, tp_calls body true)
    | LambdaOpt'(args, last, body) -> LambdaOpt'(args, last, tp_calls body true)
    | Applic'(e, exps) ->
          if in_tp
          then ApplicTP'(tp_calls e false, List.map (fun e-> tp_calls e false) exps)
          else Applic'(tp_calls e false, List.map (fun e-> tp_calls e false) exps)   
    | _-> raise X_syntax_error

and lastOf list =  (* returns last element of a non-empty list *)
    match list with
      | [x] -> x
      | _ :: t -> lastOf t
      | _-> raise X_syntax_error;;

let annotate_tail_calls e = tp_calls e false;;

let rec boxing e =
    match e with
        | Var'(v) -> (match v with
                     | VarParam(name, m) -> BoxGet'(v) 
                     | VarBound(name, _,m) -> BoxGet'(v) 
                     | VarFree(name) -> Var'(v)) 
        | Set'(v, exp) -> (match v with
                          | VarParam(name, m) -> BoxSet'(v, boxing exp) 
                          | VarBound(name, _,m) -> BoxSet'(v, boxing exp)
                          | VarFree(name) -> Set'(v, boxing exp) )
        | Const'(_) -> e
        | Or'(exps) -> Or'(List.map (fun e-> boxing e) exps)
        | If'(test, dit, dif) -> If'(boxing test, boxing dit, boxing dif)
        | Seq'(l) -> Seq'(List.map (fun e-> boxing e) l)
        | Def'(v, exp) -> Def'(v, boxing exp)
        | LambdaSimple'(args, body) -> 
                let args_to_be_boxed_list = args_for_boxing args 0 in(* args_for_boxing args body 0 [(arg1_to_be_boxed, its index),...,(argn_to_be_boxed, its index)] *)
                if args_to_be_boxed_list = []
                then LambdaSimple'(args, boxing body)
                else 
                    let body_after_Box_set_get = boxing body in
                    let init_seq_of_body = List.map (fun (arg,i)-> Set'(VarParam(arg, i), Box'(VarParam(arg,i)))) args_to_be_boxed_list in
                    (match body_after_Box_set_get with  (* preventing nested sequence *)
                                     | Seq'(l) -> LambdaSimple'(args, Seq'(List.append init_seq_of_body l)) 
                                     | _-> LambdaSimple'(args, Seq'(List.append init_seq_of_body [body_after_Box_set_get]))) 
        | LambdaOpt'(args, last, body) ->  
                let args_to_be_boxed_list = args_for_boxing (List.append args [last]) 0 in (* args_for_boxing args body 0 [(arg1_to_be_boxed, its index),...,(argn_to_be_boxed, its index)] *)
                if args_to_be_boxed_list = []
                then LambdaOpt'(args, last, boxing body)
                else 
                    let body_after_Box_set_get = boxing body in
                    let init_seq_of_body = List.map (fun (arg,i)-> Set'(VarParam(arg, i), Box'(VarParam(arg,i)))) args_to_be_boxed_list in
                    (match body_after_Box_set_get with  (* preventing nested sequence *)
                                     | Seq'(l) -> LambdaOpt'(args, last, Seq'(List.append init_seq_of_body l)) 
                                     | _-> LambdaOpt'(args, last, Seq'(List.append init_seq_of_body [body_after_Box_set_get])))
        | Applic'(e, exps) -> Applic'(boxing e, List.map (fun exp-> boxing exp) exps)
        | ApplicTP'(e, exps) -> ApplicTP'(boxing e, List.map (fun exp-> boxing exp) exps)
        | _-> raise X_syntax_error1 (* won't get here *)
        
        
and args_for_boxing args i = 
    match args with
    | [] -> []
    | [a] -> [(a,i)] 
    | a::b -> List.append [(a,i)] (args_for_boxing b (i+1))

;;

let box_set e = boxing e ;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (*struct Semantics *)






(*  boxing things:

    ▶ Read occurrence within a closure
    ▶ Write occurrence within another closure
    ▶ Both occurrences already share a rib *)

    (* 1. Seq' ([...; <write-occur>; ...; E; ...]) where E is an expr that contains a <read-occur>.
       2. Seq' ([...; <read-occur>;  ...; E; ...]) where E is an expr that contains a <write-occur>. *)
(* and args_for_boxing args body argIndex =

    match args with
    | [] -> []
    | [arg] -> check arg body [false, false, false, false, false] argIndex
    | arg :: rest -> List.append (check arg body [false, false, false, false, false] argIndex) (args_for_boxing rest body (argIndex+1)) *)
    (* if args = [] then []
    else
        let occursList = read_write_occurs_list args body in  = [(Var'1, "read"),...,(Var'n, "write")] *)
(* checks if arg needs to be boxed *)
(* and check arg body flags argIndex =
    match flags with
    (* | *)
    (* | [true,...,true] -> [(arg, argIndex)] *)
    | _-> match body with
          | Seq'(s) ->  
          |
          | *)

(* and read_write_occurs_list args body =
    match args with 
                    | [argName] -> read_write_occurs_list_per_arg argName body []
                    | argName :: restArgs -> List.append (read_write_occurs_list_per_arg argName body []) (read_write_occurs_list restArgs body)

and read_write_occurs_list_per_arg argName body l =
    match body with
        | Var'(v) -> (match v with
                     | VarParam(arg_name1, _) -> if arg_name1=argName then List.append l [(v, "read")]
                     | VarBound(arg_name1, _,_) -> if arg_name1=argName then List.append l [(v, "read")] )
        | Set'(v, exp) -> (match v with
                          | VarParam(arg_name1, _) -> if arg_name1=argName then List.append l [(v, "write")]
                          | VarBound(arg_name1, _,_) -> if arg_name1=argName then List.append l [(v, "write")] )
         
        | If'(test, dit, dif) -> List.append (List.append (read_write_occurs_list_per_arg argName test l) (read_write_occurs_list_per_arg argName dit [])) (read_write_occurs_list_per_arg argName dif [])
        | Seq'(exps) -> read_write_occurs_list_per_arg argName exps l
        | Def'(v, exp) -> read_write_occurs_list_per_arg argName exp l
        | Or'(exps) -> read_write_occurs_list_per_arg argName exps l
        | LambdaSimple'(args, body) -> read_write_occurs_list_per_arg argName body l
        | LambdaOpt'(args, last, body) -> read_write_occurs_list_per_arg argName body l
        | Applic'(e, exps) -> List.append (read_write_occurs_list_per_arg argName e l) (read_write_occurs_list_per_arg argName exps []) 
        | _-> l case Const' 

and should_be_boxed args body = 
*)
(* and change_to_box_set_get body args_list = 
    match body with
        | Var'(v) -> (match v with
                     | VarParam(name, m) -> if List.mem (name, m) args_list then BoxGet'(v) else raise X_syntax_error1
                     | VarBound(name, _,m) -> if List.mem (name, m) args_list then BoxGet'(v) else raise X_syntax_error1
                     | _-> raise X_syntax_error1) 
        | Set'(v, exp) -> (match v with
                          | VarParam(name, m) -> if List.mem (name, m) args_list then BoxSet'(v, exp) else raise X_syntax_error2
                          | VarBound(name, _,m) -> if List.mem (name, m) args_list then BoxSet'(v, exp) else raise X_syntax_error2
                          | _-> raise X_syntax_error2 )
        | If'(test, dit, dif) -> If'(change_to_box_set_get test args_list, change_to_box_set_get dit args_list, change_to_box_set_get dif args_list)
        | Seq'(exps) -> Seq'(List.map (fun e-> change_to_box_set_get e args_list) exps)
        | Def'(v, exp) -> Def'(v, change_to_box_set_get exp args_list)
        | Or'(exps) -> Or'(List.map (fun e-> change_to_box_set_get e args_list) exps)
        | LambdaSimple'(args, body) -> LambdaSimple'(args, change_to_box_set_get body args_list)
        | LambdaOpt'(args, last, body) -> LambdaOpt'(args, last, change_to_box_set_get body args_list)
        | Applic'(e, exps) -> Applic'(change_to_box_set_get e args_list, List.map (fun e-> change_to_box_set_get e args_list) exps)
        | _-> body won't get here *)