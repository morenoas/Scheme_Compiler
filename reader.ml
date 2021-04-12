
#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  |  _-> false;;
  
module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


let nt_Bool =
  let bool = PC.caten (PC.char '#') (PC.one_of_ci "tf") in
  PC.pack bool (fun (a,b) -> 
    match b with
    | 't' | 'T' -> Bool (true)
    | 'f' | 'F' -> Bool (false)
    | _-> raise PC.X_no_match);;

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let nt_Char =
    let nt_CharPrefix =  PC.pack (PC.word "#\\") (fun _-> Nil) in
    let nt_VisibleSimpleChar = PC.pack (PC.const (fun ch-> (int_of_char ch) > 32)) (fun ch-> Char(ch)) in
    let nt_NamedChar =  PC.disj_list[PC.pack (PC.word_ci "newline") (fun _-> Char(char_of_int 10));
                                     PC.pack (PC.word_ci "nul") (fun _-> Char(char_of_int 0));
                                     PC.pack (PC.word_ci "page") (fun _-> Char(char_of_int 12));
                                     PC.pack (PC.word_ci "return") (fun _-> Char(char_of_int 13));
                                     PC.pack (PC.word_ci "space") (fun _-> Char(char_of_int 32));
                                     PC.pack (PC.word_ci "tab") (fun _-> Char(char_of_int 9));] in
    PC.pack (PC.caten nt_CharPrefix (PC.disj nt_NamedChar nt_VisibleSimpleChar))
            (fun (prefix,ch)-> ch);;

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let rec gcd a b =
      if a = b then a
      else if a > b then gcd (a - b) b
      else gcd a (b - a);;

let char_to_digit c = (int_of_char c) - (int_of_char '0');;

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let nt_Number = 
    let nt_digits = PC.plus (PC.range '0' '9') in
    let nt_Natural = PC.pack nt_digits
                             list_to_string in
    (* let nt_Natural = PC.pack nt_digits 
                             (fun digits-> (List.fold_left
                              (fun x y -> 10 * x + (char_to_digit y)) 0 digits)) in    *)
    let nt_MinusInteger = 
      PC.pack (PC.caten(PC.char '-') nt_Natural)
              (fun (_, num)-> "-" ^ num ) in
    let nt_PlusInteger = 
      PC.pack (PC.caten(PC.char '+') nt_Natural)
              (fun (_, num)->  num ) in

    let nt_Integer = PC.disj_list[nt_MinusInteger; nt_PlusInteger; nt_Natural] in
    let nt_IntegerPacked = PC.pack nt_Integer (fun str-> Number(Fraction(int_of_string str, 1))) in

    let nt_Fraction = 
      PC.pack (PC.caten_list[nt_Integer; PC.pack (PC.char '/') (fun ch-> "/"); nt_Natural]) 
              (fun list-> match list with
                [num; _; denom] ->
                    let num = int_of_string num in
                    let numForGcd =  if num < 0 then -1*num else num in
                    let denom = int_of_string denom in
                    let denomForGcd =  if denom < 0 then -1*denom else denom in
                    let gcd1 = gcd numForGcd denomForGcd in
                    Number(Fraction(num/gcd1, denom/gcd1))
                | _-> raise PC.X_no_match) in
     
    let nt_FloatNotPacked = (PC.caten_list[nt_Integer; PC.pack (PC.char '.') (fun ch-> "."); nt_Natural]) in
    let nt_FloatString = PC.pack nt_FloatNotPacked
                                 (fun list-> match list with
                                  | [int; _; natural]->  int ^ "." ^ natural 
                                  | _-> raise PC.X_no_match) in 
    let nt_Float = PC.pack nt_FloatNotPacked
                             (fun list-> match list with
                             | [befDot; dot; aftDot] -> Number(Float(float_of_string (befDot ^ dot ^ aftDot)))
                             | _-> raise PC.X_no_match) in

    let nt_ScientificNotation = 
      PC.pack (PC.caten_list[PC.disj nt_FloatString nt_Integer; PC.pack (PC.char_ci 'e') (fun _-> "e"); nt_Integer])
              (fun list-> match list with
              | [befE; e; aftE]-> Number(Float(float_of_string (befE ^ e ^ aftE)))
              | _-> raise PC.X_no_match) in
            
    let nt_SymbolChar = PC.pack (PC.disj_list[ PC.range '0' '9'; PC.range_ci 'a' 'z'; PC.one_of ".!$^*-_=+<>?/:"])
                                (fun sym-> 'a') in


    PC.not_followed_by (PC.disj_list [nt_ScientificNotation; nt_Fraction; nt_Float; nt_IntegerPacked]) nt_SymbolChar ;;
    

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let nt_String =
  let nt_StringLiteralChar = PC.const (fun ch -> ch != '\"' && ch != '\\') in
  let nt_StringMetaChar = PC.pack (PC.caten (PC.char '\\') (PC.one_of("\\\"tfnr"))) 
                                  (fun (backslash, metaCh)-> match metaCh with
                                  | 't' -> (char_of_int 9) | 'f' -> (char_of_int 12) | 'n' -> (char_of_int 10) | 'r' -> (char_of_int 13)
                                  | char -> char) in 

  let nt_StringChar = PC.disj nt_StringLiteralChar nt_StringMetaChar in
  
  PC.pack (PC.caten(PC.caten (PC.char '\"') (PC.star nt_StringChar)) (PC.char '\"'))
          (fun ((dquote1, str), dquote2)-> String(list_to_string str)) ;;
(* --------------------------------------------------------------------------------------------------------------------------------- *)

let nt_Symbol =
  let nt_SymbolChar = PC.disj_list[ PC.range '0' '9'; PC.range_ci 'a' 'z'; PC.one_of ".!$^*-_=+<>?/:"] in
  (* let nt_SymbolChar = PC.disj nt_SymbolCharNoDot (PC.char '.') in *)
  let nt_SymbolCharPlus = PC.plus nt_SymbolChar in

  PC.pack nt_SymbolCharPlus
          (fun charList-> match charList with
            | ['.'] -> raise PC.X_no_match
            | chList -> Symbol(list_to_string (List.map (fun upper-> Char.lowercase_ascii upper) chList)));;

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let rec nt_List s =

  let nt_EmptyList = PC.pack (PC.caten_list[PC.pack (PC.char '(') (fun _->Nil); nt_Whitespaces; PC.pack (PC.char ')') (fun _->Nil)])
                             (fun _-> Nil) in

  (* PC.pack (PC.caten_list[PC.char '('; PC.delayed nt_SexprStar; PC.char ')'])  *)
  let nt_RegularList =
   PC.pack (PC.caten(PC.caten (PC.char '(') nt_SexprPlus) (PC.char ')'))
          (fun ((l, exps), r) -> List.fold_right (fun a b -> Pair(a,b)) exps Nil ) in
          
 let nt_DottedList = 
  PC.pack (PC.caten_list[PC.pack (PC.char '(') (fun _->[Nil]); nt_SexprPlus; PC.pack (PC.char '.') (fun _->[Nil]); PC.pack nt_Sexpr (fun exp->[exp] ); PC.pack (PC.char ')') (fun _->[Nil])]) 
          (fun list-> match list with
          | [l; exps; dot; [exp]; r] -> List.fold_right (fun a b -> Pair(a,b)) exps exp
          | _-> raise PC.X_no_match) in
    
  PC.disj_list[nt_EmptyList; nt_RegularList; nt_DottedList]  s


and nt_Sexpr s =
               PC.pack (PC.caten_list[nt_Whitespaces;
                                      PC.disj_list [nt_Bool; nt_Char; nt_String; nt_Number; nt_Symbol; nt_List;
                                            nt_Quoted; nt_QuasiQuoted; nt_Unquoted; nt_UnquoteAndSpliced] ; 
                                      nt_Whitespaces]) 
                       (fun list-> match list with 
                       | [_; exp; _]-> exp 
                       | _-> raise PC.X_no_match) s  
           

and nt_SexprPlus s = (PC.plus nt_Sexpr) s
and nt_SexprStar s = (PC.star nt_Sexpr) s
                               

(* --------------------------------------------------------------------------------------------------------------------------------- *)

and nt_Quoted s = PC.pack (PC.caten_list[PC.pack (PC.char '\'') (fun _-> Nil); nt_Whitespaces; nt_Sexpr])
                                  (fun list-> match list with 
                                       |[q; _; exp] -> Pair(Symbol("quote"), Pair(exp, Nil))
                                       | _-> raise PC.X_no_match) s 

and nt_QuasiQuoted s = PC.pack (PC.caten_list[PC.pack (PC.char '`') (fun _-> Nil); nt_Whitespaces; nt_Sexpr])
                                  (fun list-> match list with 
                                       |[q; _; exp] -> Pair(Symbol("quasiquote"), Pair(exp, Nil))
                                       | _-> raise PC.X_no_match) s

and nt_Unquoted s = PC.pack (PC.caten_list[PC.pack (PC.char ',') (fun _-> Nil); nt_Whitespaces; nt_Sexpr])
                                  (fun list-> match list with 
                                       |[q; _; exp] -> Pair(Symbol("unquote"), Pair(exp, Nil))
                                       | _-> raise PC.X_no_match) s

and nt_UnquoteAndSpliced s = PC.pack (PC.caten_list[PC.pack (PC.word ",@") (fun _-> Nil); nt_Whitespaces; nt_Sexpr])
                                  (fun list-> match list with 
                                       |[q; _; exp] -> Pair(Symbol("unquote-splicing"), Pair(exp, Nil))
                                       | _-> raise PC.X_no_match) s

(* --------------------------------------------------------------------------------------------------------------------------------- *)


and nt_LineComment s = 
    let nt_notNewLine = PC.star (PC.const (fun ch-> (int_of_char ch) != 10 && (int_of_char ch) != 3)) in (* 3 is end of input, 10 is a new line*)
    PC.pack (PC.caten_list[PC.pack (PC.char ';') (fun _-> ' ');
                           PC.pack nt_notNewLine (fun _-> ' ');
                           PC.pack (PC.disj (PC.char (char_of_int 10)) (PC.char (char_of_int 3))) (fun _-> ' ')])
            (fun comment-> ' ') s
    
and nt_SexprComments s =
    PC.pack (PC.caten_list[PC.pack (PC.word "#;") (fun _-> ' ');
                           PC.pack (PC.star (PC.nt_whitespace)) (fun spaces-> ' ');
                           PC.pack nt_Sexpr (fun _-> ' ')])
            (fun  list-> match list with
            | [_; _; _] -> ' '
            | _-> raise PC.X_no_match) s

and nt_Whitespaces s =   PC.pack (PC.star (PC.disj_list[nt_LineComment; nt_SexprComments; PC.nt_whitespace]))
                                 (fun _-> Nil) s ;;

(* --------------------------------------------------------------------------------------------------------------------------------- *)

let read_sexprs string = 
  let parsed = nt_SexprStar (string_to_list string) in
  match parsed with
  | (p, _) -> p ;;
     
 end;; (* struct Reader *)