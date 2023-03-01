(* 
   The Parsed AST 
*) 
type var = string 

type loc = Lexing.position 

type type_expr = 
   | TEpoly
   | TEint 
   | TEbool 
   | TEunit 
   | TEref of type_expr 
   | TEarrow of type_expr * type_expr
   | TEproduct of type_expr * type_expr
   | TEunion of type_expr * type_expr

type oper = ADD | MUL | DIV | SUB | LT | AND | OR | EQ | EQB | EQI

type unary_oper = NEG | NOT 

type nested_binding =
   | BindingUnit of var * type_expr
   | BindingPair of nested_binding * nested_binding

type expr = 
       | Unit of loc  
       | What of loc 
       | Var of loc * var
       | Integer of loc * int
       | Boolean of loc * bool
       | UnaryOp of loc * unary_oper * expr
       | Op of loc * expr * oper * expr
       | If of loc * expr * expr * expr
       | Pair of loc * expr * expr
       | Fst of loc * expr 
       | Snd of loc * expr 
       | Inl of loc * type_expr * expr 
       | Inr of loc * type_expr * expr 
       | Case of loc * expr * lambda * lambda 

       | While of loc * expr * expr 
       | Seq of loc * (expr list)
       | Ref of loc * expr 
       | Deref of loc * expr 
       | Assign of loc * expr * expr

       | Lambda of loc * lambda 
       | TupleLambda of loc * tuple_lambda 
       | App of loc * expr * expr 
       | Let of loc * var * type_expr * expr * expr
       | LetTuple of loc * nested_binding * expr * expr
       | LetFun of loc * var * lambda * type_expr * expr
       | LetTupleFun of loc * var * tuple_lambda * type_expr * expr
       | LetRecFun of loc * var * lambda * type_expr * expr
       | LetRecTupleFun of loc * var * tuple_lambda * type_expr * expr

       | Raise of loc * expr
       | Try of loc * expr * var * type_expr * expr

and lambda = var * type_expr * expr 
and tuple_lambda = nested_binding * expr
val loc_of_expr : expr -> loc 
val type_of_nested_binding : nested_binding -> type_expr
val vars_of_nested_binding : nested_binding -> (var * type_expr) list
val string_of_loc : loc -> string 

(* printing *) 
val string_of_unary_oper : unary_oper -> string 
val string_of_oper : oper -> string 
val string_of_type : type_expr -> string 
val string_of_expr : expr -> string 
val print_expr : expr -> unit 
val eprint_expr : expr -> unit


