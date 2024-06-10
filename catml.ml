(*
   Homework 4, Problem 7: Completing the CatML interpreter.

   In this OCaml code file you will find the beginning of various functions with
   COMPLETE ME tags in the comments, that you must complete to obtain a *correct*
   interpreter for the CatML language. This includes: subst, closed, and redx.

   Both the tracer and stepper functions (with pretty printing) have been completed
   for you and can be used for testing examples as you work on the assignment. Example
   expressions for testing can be found in the course github repository.

   You should renamte this file as catml.ml and submit once completed. Your submission 
   must be executable OCaml code.
*)

(*
   Abstract Syntax
   ---------------
  
   The expr datatype defines the ASTs for CatML. The mapping from CatML concrete syntax
   to abstract syntax is as follows, in full detail.
 
   [[True]] = Bool(true)
   [[False]] = Bool(false)
   [[n]] = Nat(n)           for any natural number n
   [[x]] = Var(Ident("x"))       for any variable x
   [[e1 + e2]] = Plus([[e1]], [[e2]])
   [[e1 - e2]] = Minus([[e1]], [[e2]])
   [[e1 And e2]] = And([[e1]], [[e2]])
   [[e1 Or e2]] = Or([[e1]], [[e2]])
   [[Not e]] = Not([[e]])
   [[If e1 Then e2 Else e3]] = If([[e1]], [[e2]], [[e3]])
   [[(e1, e2)]] = Pair([[e1]], [[e2]])
   [[Fst(e)]] = Fst([[e]])
   [[Snd(e)]] = Snd([[e]])
   [[e1 e2]] = Appl([[e1]], [[e2]])
   [[Let x = e1 in e2]] = Let(Ident("x"), [[e1]], [[e2]])
   [[(Fun x . e)]] = Fun(Ident("x"), [[e]])
   [[(Fix z . x . e)]] = Fix(Ident("z"), Ident("x"), [[e]])
*)

type ident = Ident of string

type expr =
     (* boolean expression forms *)
     Bool of bool | And of expr * expr | Or of expr * expr | Not of expr   
     (* arithmetic expression forms *)
   | Nat of int | Plus of expr * expr | Minus of expr * expr | Equal of expr * expr  
     (* functional expression forms *)
   | Function of ident * expr | Appl of expr * expr | Var of ident
     (* pairs *)
   | Pair of expr * expr | Fst of expr | Snd of expr
     (* other forms *)
   | If of expr * expr * expr | Let of ident * expr * expr | Fix of ident * ident * expr

exception AssignmentIncomplete

(*
   Closed expression check
   ------------------------

   Since reduction is defined only on closed expressions, we need to implement
   a check to ensure that an input expression is closed. Since closure is preserved
   by reduction, this check can be performed once statically on source code,
   as in tracer and stepper below.									     
   closed : Dast.expr -> Dast.ident list -> bool
   in : an expression e and an identifier list ilist
   out : true iff e is closed, assuming every element of ilist is 
         a bound variable
*)
let rec closed e ident_list = match e with Var(Ident i) -> List.mem (Ident i) ident_list
   | And(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | Or(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | Not(e1) -> closed e1 ident_list
   | Plus(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | Minus(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | Equal(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | If(e1, e2, e3) -> (closed e1 ident_list) && (closed e2 ident_list) && (closed e3 ident_list)
   | Pair(e1, e2) -> (closed e1 ident_list) && (closed e2 ident_list)
   | Fst(e1) -> closed e1 ident_list
   | Snd(e1) -> closed e1 ident_list
   | Function(Ident i, e1) -> let x = (Ident i) :: ident_list in (closed e1 x)
   | Fix(Ident z, Ident i, e1) -> let x = (Ident z) :: (Ident i) :: ident_list in (closed e1 x)
   | Let(Ident i, e1, e2) -> (closed e1 ident_list) && (let x = (Ident i) :: ident_list in (closed e2 x))
   | Appl(e1, e2) -> closed e1 ident_list && closed e2 ident_list
   | Nat(n) -> true
   | Bool(b) -> true

(*
   Substitution
   ------------

   We implement substitution as defined symbolically, to obtain a substution-based
   semantics in the interpreter.
  
   subst : Dast.expr -> Dast.expr -> Dast.ident -> Dast.expr
   in : expression e1, expression e2, identifier id
   out : e1[e2/id] 
*)
let rec subst e1 e2 id = match e1 with Var(Ident i) -> (match id with Ident i2 -> if i = i2 then e2 else Var(Ident i))
   | And(fir, sec) -> And(subst fir e2 id, subst sec e2 id)
   | Or(fir, sec) -> Or(subst fir e2 id, subst sec e2 id)
   | Not(fir) -> Not(subst fir e2 id)
   | Plus(fir, sec) -> Plus(subst fir e2 id, subst sec e2 id)
   | Minus(fir, sec) -> Minus(subst fir e2 id, subst sec e2 id)
   | Equal(fir, sec) -> Equal(subst fir e2 id, subst sec e2 id)
   | If(fir, sec, thir) -> If(subst fir e2 id, subst sec e2 id, subst thir e2 id)
   | Pair(fir, sec) -> Pair(subst fir e2 id, subst sec e2 id)
   | Fst(fir) -> Fst(subst fir e2 id)
   | Snd(fir)-> Snd(subst fir e2 id)
   | Let(Ident i, fir, sec) -> (match id with Ident i2 -> if not (i = i2) then (Let(Ident i, subst fir e2 id, subst sec e2 id)) else Let(Ident i, subst fir e2 id, sec))
   | Function(Ident i, fir) -> (match id with Ident i2 -> if not (i = i2) then (Function(Ident i, subst fir e2 id)) else e1)
   | Fix(Ident z, Ident i, fir) -> (match id with Ident i2 -> if (not (i = i2) && not (i2 = z)) then (Fix(Ident z, Ident i, subst fir e2 id)) else e1)
   | Appl(fir, sec) -> Appl(subst fir e2 id, subst sec e2 id)
   | _ -> e1

(*
   Value predicate
   ---------------

   Checking whether a given expression is a value is critical for the operational 
   semantics. 

   isval : expr -> bool
   in : expression e
   out : true iff e is a value
*)
let rec isval = function 
     Nat(_) -> true
   | Bool(_) -> true
   | Function(_) -> true
   | Fix(_) -> true
   | Pair(e1, e2) -> isval e1 && isval e2
   | _ -> false

exception NotReducible
(*
   Single step reduction
   ---------------------

   Single (aka small) step reduction is the heart of the operational semantics. Pattern
   matching allows a tight connection with the symbolic definition of the semantics.
   
   redx : expr -> expr
   in : AST [[e]]
   out : AST [[e']] such that e -> e' in the operational semantics
   side effect : exception NotReducible raised if [[e]] isn't reducible in implementation.
*)
exception StuckExpression;;
let rec redx e = match e with
     Not(Bool(b)) -> Bool(not b)
   | And(Bool(b1), Bool(b2)) -> Bool(b1 && b2)
   | Or(Bool(b1), Bool(b2)) -> Bool(b1 || b2)
   | Not(e) -> Not(redx e)
   | And(e1,e2) -> if isval e1 then And(e1, redx e2) else And(redx e1, e2)
   | Or(e1,e2) -> if isval e1 then Or(e1, redx e2) else Or(redx e1, e2)
   | Plus(Nat(n1), Nat(n2)) -> Nat(n1 + n2)
   | Minus(Nat(n1), Nat(n2)) -> if n1 > n2 then Nat(n1-n2) else Nat(0)
   | Equal(Nat(n1), Nat(n2)) -> Bool(n1 = n2)
   | Plus(e1,e2) -> if isval e1 then Plus(e1, redx e2) else Plus(redx e1, e2)
   | Minus(e1, e2) -> if isval e1 then Minus(e1, redx e2) else Minus(redx e1, e2)
   | Equal(e1, e2) -> if isval e1 then Equal(e1, redx e2) else Equal(redx e1, e2)
   | If(Bool(true), e, _) -> e
   | If(Bool(false), _, e) -> e
   | If(e1, e2, e3) -> If(redx e1, e2, e3)
   | Let(Ident i, e2, e3) -> if isval e2 then subst e3 e2 (Ident i) else Let(Ident i, redx e2, e3)
   | Appl(Function(Ident i, e2), e3) -> if isval e3 then subst e2 e3 (Ident i) else Appl(Function(Ident i, e2), redx e3)
   | Appl(Fix(Ident z, Ident i, e2), e3) -> if isval e3 then (let e5 = subst e2 e3 (Ident i) in (subst e5 (Fix(Ident z, Ident i, e2)) (Ident z))) else Appl(Fix(Ident z, Ident i, e2), redx e3)
   | Appl(e1, e2) -> Appl(redx e1, e2)
   | Pair(e1, e2) -> if isval e1 then Pair(e1, redx e2) else Pair(redx e1, e2)
   | Fst(Pair(e1, e2)) -> e1
   | Snd(Pair(e1, e2)) -> e2
   | Fst(e) -> Fst(redx e)
   | Snd(e) -> Snd(redx e)
   | _ -> raise NotReducible;;


(*exception StuckExpression;;*)
(*
   Multistep reduction
   -------------------

   redxs : expr -> expr
   in : AST [[e]]
   out : [[v]] such that e ->* v in the operational semantics
*)
let rec redxs e = if isval e then e else redxs (try (redx e) with NotReducible -> raise StuckExpression)


open Printf;;

(*
  prettyPrint : expr -> string
  in : An expression AST [[e]].
  out : The concrete expression e in string format.
*)
let rec prettyPrint e = match e with
   | Bool true -> "True"
   | Bool false -> "False"
   | Nat n -> sprintf "%i" n
   | Var(Ident(x)) -> x
   | And (e1, e2) -> "(" ^ (prettyPrint e1) ^ " And " ^ (prettyPrint e2) ^ ")"
   | Or (e1, e2) -> "(" ^ (prettyPrint e1) ^ " Or " ^ (prettyPrint e2) ^ ")"
   | Not e1 -> "(Not " ^ (prettyPrint e1) ^ ")"
   | Plus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " + " ^ (prettyPrint e2) ^ ")"
   | Minus (e1, e2) -> "(" ^ (prettyPrint e1) ^ " - " ^ (prettyPrint e2) ^ ")"
   | Equal (e1, e2) -> "(" ^ (prettyPrint e1) ^ " = " ^ (prettyPrint e2) ^ ")"
   | If(e1, e2, e3) -> "If " ^ (prettyPrint e1) ^ 
                       " Then " ^ (prettyPrint e2) ^
                       " Else " ^ (prettyPrint e3)
   | Function(Ident(x), e) -> "(Fun " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
   | Fix(Ident(z), Ident(x), e) -> "(Fix " ^ z ^ " . " ^ x ^ " . " ^ (prettyPrint e) ^ ")"
   | Let(Ident(x), e1, e2) -> "Let " ^ x ^ " = " ^ (prettyPrint e1) ^ " In\n" ^ (prettyPrint e2)
   | Appl(e1, e2) -> (prettyPrint e1) ^ " " ^ (prettyPrint e2)
   | Pair(e1, e2) -> "(" ^ (prettyPrint e1) ^ ", " ^ (prettyPrint e2) ^ ")"
   | Fst(e1) -> 
      (match e1 with Pair(_) -> "Fst" ^  (prettyPrint e1) 
                  | _ ->  "Fst(" ^  (prettyPrint e1) ^ ")")
   | Snd(e1) -> 
      (match e1 with Pair(_) -> "Snd" ^  (prettyPrint e1) 
                  | _ ->  "Snd(" ^  (prettyPrint e1) ^ ")")


exception NotClosed;;

(*
  pretty_trace : expr -> bool -> unit
  in : AST [[e]]
  out : () 
  side effects : prints intermediate expressions (aka the reduction trace) 
    during evaluation; if stepper flag is on, blocks on keystroke between 
    reductions.  
*)
let rec pretty_trace e stepper =
  (printf "%s" (prettyPrint e); if stepper then ignore (read_line()) else ();
   if (isval e) then (printf "\n"; flush stdout) else
     try
       (
         let e' = redx e in
         (printf "->\n"; flush stdout; pretty_trace e' stepper)
       )
     with NotReducible ->  (printf "  (Bad, Stuck Expression)\n"; flush stdout))

(*
  stepper : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : Blocks on keystroke between reductions, prints intermediate 
    expressions (aka the reduction trace) during evaluation; 
    raises NotClosed if e is not closed.     
*)
let rec stepper e = if (closed e []) then (pretty_trace e true) else raise NotClosed ;;
(*
  tracer : expr -> expr
  in : AST [[e]]
  out : [[v]] such that e ->* v in the operational semantics
  side effects : prints intermediate expressions (aka the reduction trace) during evaluation; 
    raises NotClosed if e is not closed. 
*)
let rec tracer e =  if (closed e []) then (pretty_trace e false) else raise NotClosed;;
