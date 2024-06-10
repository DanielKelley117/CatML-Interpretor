(* 
   Homework 5, Problem 4: Completing the CatML_tau type checker.

   The function typecheck needs to be completed to obtain correct type
   checking (search for the COMPLETE ME comment).  Some cases have
   been completed already. These should implement the type derivation
   rules (see the Definition of catmlt.pdf on Brightspace in the
   Supplementary Materials module for a complete listing).

   A top-level typing function with pretty printing (prptyping) has
   been completed for you and can be used for testing examples as you
   work on the assignment. The online type checker (link also
   Supplementary Materials) can be used to easily generate ASTs and
   test examples (example programs are available in
   catmlt-examples.cml in the course GitHub repo):

      http://ceskalka.w3.uvm.edu/225/catml/catmlf.php

   Take special note of the Abstract Syntax definition, that includes
   a description of how type environments have been implemented.

   You should submit this file once completed. Your submission must be
   executable OCaml code.  *)

(*
   Abstract Syntax
   ---------------

   TYPES

   The tau datatype defines the ASTs for CatML_tau types. The mapping from concrete
   type syntax to abstract type syntax is defined as follows. 

   [[Nat]] = Natt
   [[Bool]] = Boolt
   [[tau_1 * tau_2]] = Prod([tau_1]], [[tau_2]])
   [[tau_1 -> tau_2]] = Arrow([[tau_1]], [[tau_2]])

   TYPE ENVIRONMENTS
   
   We implement identifiers using the type ident, and we define an environment type as 
   (ident * tau) lists. Letting 0 denote the empty environment, we can define the following
   concrete-to-abstract conversion for environments as follows. 

   [[0]] = []
   [[Gamma; x : tau]] = (Ident("x"), [[tau]])::[[Gamma]]

   The functions extend and lookup are already provided, to add a new type binding to an 
   environment and to look up a type binding in the environment.

   EXPRESSIONS

   The expr datatype defines the ASTs for CatML_tau expressions. The mapping from concrete syntax
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
   [[(Fun (x : tau) . e)]] = Fun(Ident("x"), [[tau]], [[e]])
   [[(Fix z . (x : tau_1) : tau_2 . e)]] = Fix(Ident("z"), Ident("x"), [[tau_1]], [[tau_2]], [[e]])
*)

type ident = Ident of string

(* type syntax *)
type tau = Natt | Boolt | Prod of tau * tau | Arrow of tau * tau 

(* expression syntax *)
type expr =
     (* boolean expression forms *)
     Bool of bool | And of expr * expr | Or of expr * expr | Not of expr   
     (* arithmetic expression forms *)
   | Nat of int | Plus of expr * expr | Minus of expr * expr | Equal of expr * expr  
     (* functional expression forms *)
   | Function of ident * tau * expr | Appl of expr * expr | Var of ident
     (* pairs *)
   | Pair of expr * expr | Fst of expr | Snd of expr
     (* control forms *)
   | If of expr * expr * expr | 
     Let of ident * expr * expr |
     Fix of ident * ident * tau * tau * expr 

(* this exception should get raised when a type error is encountered *)
exception TypeError

exception AssignmentIncomplete

(* type environments datatype *)
type environment = (ident * tau) list

(* 
   extend : environment -> ident * tau -> environment
   in : environment gamma, identifier, type pair (x,tau)
   out : (gamma; x : tau)
*)
let rec extend gamma (x,y) = (x,y)::gamma

(* 
   lookup : ident -> environment -> tau
   in : identifier x, environment gamma
   out : gamma(x)
*)
let rec lookup x gamma = 
  match gamma with 
    [] -> raise TypeError
  | (x',t)::bs -> if x = x' then t else lookup x bs

(* 
   typecheck : environment -> expr -> tau
   in : type environment [[gamma]], TD expression [[e]]
   out : [[tau]] iff ([[gamma]] |- [[e]] : [[tau]]) is a valid type judgement
   side effect: raises TypeError if e is not well-typed
*)
let rec typecheck gamma e = 
  match e with
  | Nat(x) -> Natt
  | Bool(b) -> Boolt
  | Var(x) -> lookup x gamma
  | Plus(x, y) -> 
     (match (typecheck gamma x, typecheck gamma y) with 
	(Natt, Natt) -> Natt
       |	_ -> raise TypeError)
  | Minus(x, y) -> 
      (match (typecheck gamma x, typecheck gamma y) with 
            (Natt, Natt) -> Natt
           |   _ -> raise TypeError)
  | Equal(x, y) ->
        (match (typecheck gamma x, typecheck gamma y) with
                (Natt, Natt) -> Boolt
                 |  _ -> raise TypeError)
  | And(x, y) ->
       (match (typecheck gamma x, typecheck gamma y) with
               (Boolt, Boolt) -> Boolt
                | _ -> raise TypeError)
  | Or(x, y) -> 
       (match (typecheck gamma x, typecheck gamma y) with
               (Boolt, Boolt) -> Boolt
               | _ -> raise TypeError)
  | Not(x) -> 
        (match (typecheck gamma x) with
                Boolt -> Boolt
                | _ -> raise TypeError)
  | If(x, y, z) ->
        (match (typecheck gamma x, typecheck gamma y, typecheck gamma z) with
                (Boolt, t1, t2) -> if t1 = t2 then t1 else raise TypeError
                | _ -> raise TypeError)
  | Pair(x, y) ->
         (match (typecheck gamma x, typecheck gamma y) with
                 (t1, t2) -> Prod (t1, t2))
  | Fst(x) -> 
       (match (typecheck gamma x) with 
               Prod(t1, t2) -> t1
               | _ -> raise TypeError)
  | Snd(x) ->
        (match (typecheck gamma x) with
                Prod(t1, t2) -> t2
                | _ -> raise TypeError)
  | Let(x, y, z) ->
              (match (typecheck gamma y) with
               t1 -> let gammaR = extend gamma (x, t1) in typecheck gammaR z)
  | Function(x, t, y) ->
                   (let gammaR = extend gamma (x, t) in Arrow(t, typecheck gammaR y))
  | Fix(z, x, t1, t2, e1) ->
                    (let gammaR = extend gamma (x, t1) in let gammaRR = extend gammaR (z, Arrow(t1, t2)) in 
                     match (typecheck gammaRR e1) with
                     t3 -> if t3 = t2 then Arrow(t1, t2) else raise TypeError)
  | Appl(x, y) -> 
                 (match (typecheck gamma x) with
                        Arrow(t1, t2) -> if t1 = (typecheck gamma y) then t2 else raise TypeError
                        | _ -> raise TypeError)

(* 
   typing : expr -> tau
   in : expression e
   out : tau such that e : tau
   side effect: raises TypeError if e is not well-typed
   note : this is the top-level function used by the interpreter, and is 
          defined in terms of typecheck; there is no need to alter this 
          function in any way
*)
let typing e = typecheck [] e

(*
  prptau : tau -> string
  in : A type AST [[tau]].
  out : The concrete expression tau in string format.
*)
let rec prptau = function
    Natt -> "Nat"
  | Boolt -> "Bool"
  | Prod(t1,t2) -> "(" ^ prptau t1 ^ " * " ^ prptau t2 ^ ")"
  | Arrow(t1,t2) -> "(" ^ prptau t1 ^ " -> " ^ prptau t2 ^ ")"

(*
  prpexpr : expr -> string
  in : An expression AST [[e]].
  out : The concrete expression e in string format.
*)
let rec prpexpr e = match e with
   | Bool true -> "True"
   | Bool false -> "False"
   | Nat n -> string_of_int n
   | Var(Ident(x)) -> x
   | And (e1, e2) -> "(" ^ (prpexpr e1) ^ " And " ^ (prpexpr e2) ^ ")"
   | Or (e1, e2) -> "(" ^ (prpexpr e1) ^ " Or " ^ (prpexpr e2) ^ ")"
   | Not e1 -> "(Not " ^ (prpexpr e1) ^ ")"
   | Plus (e1, e2) -> "(" ^ (prpexpr e1) ^ " + " ^ (prpexpr e2) ^ ")"
   | Minus (e1, e2) -> "(" ^ (prpexpr e1) ^ " - " ^ (prpexpr e2) ^ ")"
   | Equal (e1, e2) -> "(" ^ (prpexpr e1) ^ " = " ^ (prpexpr e2) ^ ")"
   | If(e1, e2, e3) -> "If " ^ (prpexpr e1) ^ 
                       " Then " ^ (prpexpr e2) ^
                       " Else " ^ (prpexpr e3)
   | Function(Ident(x), t, e) -> "(Fun (" ^ x ^ " : " ^ prptau t ^ ") . " ^ (prpexpr e) ^ ")"
   | Fix(Ident(z), Ident(x), t1, t2, e) -> 
        "(Fix " ^ z ^ " . (" ^ x ^ " : " ^ prptau t1 ^ ") : " ^ prptau t2 ^ " . " ^ (prpexpr e) ^ ")"
   | Let(Ident(x), e1, e2) -> "Let " ^ x ^ " = " ^ (prpexpr e1) ^ " In\n" ^ (prpexpr e2)
   | Appl(e1, e2) -> (prpexpr e1) ^ " " ^ (prpexpr e2)
   | Pair(e1, e2) -> "(" ^ (prpexpr e1) ^ ", " ^ (prpexpr e2) ^ ")"
   | Fst(e1) -> 
      (match e1 with Pair(_) -> "Fst" ^  (prpexpr e1) 
                  | _ ->  "Fst(" ^  (prpexpr e1) ^ ")")
   | Snd(e1) -> 
      (match e1 with Pair(_) -> "Snd" ^  (prpexpr e1) 
                  | _ ->  "Snd(" ^  (prpexpr e1) ^ ")")
(*
   prptyping : expr -> unit
   in : An expression AST [[e]].
   out : unit.
   side effects: prints "e : tau" to stdout if e : tau is valid, otherwise raises TypeError
*) 
let prptyping e = let t = typing e in print_string (prpexpr e ^ " : " ^ prptau t ^ "\n")
