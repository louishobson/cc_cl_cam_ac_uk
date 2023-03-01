

(*   translate_expr : Past.expr -> Ast.expr 
     Translates parsed AST to internal AST : 
     1) drop types 
     2) remove let 
     ) replace "?" (What) with unary function call 

  Note : our front-end drops type information.  Is this really a good idea? 
  Could types be useful in later phases of the compiler? 

*) 

type translate_nested_binding_cont = 
     | EXPAND of Past.nested_binding * string
     | EXPAND_LEFT of Past.nested_binding * string
     | EXPAND_RIGHT of Past.nested_binding * string

let translate_uop = function 
  | Past.NEG -> Ast.NEG 
  | Past.NOT -> Ast.NOT 

let translate_bop = function 
  | Past.ADD -> Ast.ADD 
  | Past.MUL -> Ast.MUL
  | Past.DIV -> Ast.DIV
  | Past.SUB -> Ast.SUB
  | Past.LT -> Ast.LT
  | Past.AND -> Ast.AND
  | Past.OR -> Ast.OR
  | Past.EQI -> Ast.EQI
  | Past.EQB -> Ast.EQB
  | Past.EQ  -> Errors.complain "internal error, translate found a EQ that should have been resolved to EQI or EQB"


let rec translate_expr = function
    | Past.Unit l            -> Ast.Unit l
    | Past.What l            -> Ast.UnaryOp(l, Ast.READ, (Ast.Unit l))
    | Past.Var(l, x)         -> Ast.Var(l, x)
    | Past.Integer(l, n)     -> Ast.Integer(l, n)
    | Past.Boolean(l, b)     -> Ast.Boolean(l, b)
    | Past.UnaryOp(l, op, e) -> Ast.UnaryOp(l, translate_uop op, translate_expr e)
    | Past.Op(l, e1, op, e2) -> Ast.Op(l, translate_expr e1, translate_bop op, translate_expr e2)
    | Past.If(l, e1, e2, e3) -> Ast.If(l, translate_expr e1, translate_expr e2, translate_expr e3)
    | Past.Pair(l, e1, e2)   -> Ast.Pair(l, translate_expr e1, translate_expr e2)
    | Past.Fst(l, e)         -> Ast.Fst(l, translate_expr e)
    | Past.Snd(l, e)         -> Ast.Snd(l, translate_expr e)
    | Past.Inl(l, _, e)       -> Ast.Inl(l, translate_expr e)
    | Past.Inr(l, _, e)       -> Ast.Inr(l, translate_expr e)
    | Past.Case(l, e, l1, l2) ->
         Ast.Case(l, translate_expr e, translate_lambda l l1, translate_lambda l l2)
    | Past.Lambda(l, lam)      -> Ast.Lambda(translate_lambda l lam)
    | Past.TupleLambda(l, tlam)      -> Ast.Lambda(translate_tuple_lambda l tlam)
    | Past.App(l, e1, e2)    -> Ast.App(l, translate_expr e1, translate_expr e2)
    (* 
       Replace "let" with abstraction and application. For example, translate 
        "let x = e1 in e2 end" to "(fun x -> e2) e1" 
    *) 
    | Past.Let(l, x, _, e1, e2) ->
         Ast.App(l, Ast.Lambda(l, x, translate_expr e2), translate_expr e1)
     | Past.LetTuple(l, nb, e1, e2) ->
          Ast.App(l, Ast.Lambda(translate_tuple_lambda l (nb, e2)), translate_expr e1)
    | Past.LetFun(l, f, lam, _, e)     ->
         Ast.LetFun(l, f, translate_lambda l lam, translate_expr e)
     | Past.LetTupleFun(l, f, tup_lam, _, e)     ->
          Ast.LetFun(l, f, translate_tuple_lambda l tup_lam, translate_expr e)
    | Past.LetRecFun(l, f, lam, _, e)     ->
         Ast.LetRecFun(l, f, translate_lambda l lam, translate_expr e)
     | Past.LetRecTupleFun(l, f, tup_lam, _, e)     ->
          Ast.LetRecFun(l, f, translate_tuple_lambda l tup_lam, translate_expr e)

    | Past.Seq(l, el) -> Ast.Seq(l, List.map translate_expr el)
    | Past.While(l, e1, e2) -> Ast.While(l, translate_expr e1, translate_expr e2)
    | Past.Ref(l, e) -> Ast.Ref(l, translate_expr e)
    | Past.Deref(l, e) -> Ast.Deref(l, translate_expr e)
    | Past.Assign(l, e1, e2) -> Ast.Assign(l, translate_expr e1, translate_expr e2)

    | Past.Raise(l, e) -> Ast.Raise(l, translate_expr e)
    | Past.Try(l, e1, x, _, e2) -> Ast.Try(l, translate_expr e1, (l, x, translate_expr e2))

and translate_lambda l (x, _, body) = (l, x, translate_expr body)

(* This function takes a Past.TupleLambda and converts it to a an Ast.Lambda *)
and translate_tuple_lambda l (nb, body) = 
     (* A reference to an int which is incremented to create unique variables *)
     let varnum = ref 0 in
     (* Translates a nested binding into a series of Past.Let expressions
      * nbs is an array of 'expansions' yet to be performed.
      *)
     let rec translate_nested_binding ( nbs : translate_nested_binding_cont list ) = match nbs with
          | EXPAND(Past.BindingPair(nb_l, nb_r), varname) :: nbs ->
               translate_nested_binding (EXPAND_LEFT(nb_l, varname) :: EXPAND_RIGHT(nb_r, varname) :: nbs)

          | EXPAND(Past.BindingUnit(x, t), varname) :: nbs ->
               Past.Let(l, x, t, Past.Var(l, varname),
                    translate_nested_binding nbs)

          | EXPAND_LEFT(Past.BindingPair(nb_l, nb_r) as nb, varname) :: nbs -> 
               let new_varname = (varnum := !varnum + 1; "__nb_" ^ (string_of_int !varnum)) in
               Past.Let(l, new_varname, Past.type_of_nested_binding nb, Past.Fst(l, Past.Var(l, varname)),
                    (translate_nested_binding (EXPAND(nb, new_varname) :: nbs)))

          | EXPAND_RIGHT(Past.BindingPair(nb_l, nb_r) as nb, varname) :: nbs -> 
               let new_varname = (varnum := !varnum + 1; "__nb_" ^ (string_of_int !varnum)) in
               Past.Let(l, new_varname, Past.type_of_nested_binding nb, Past.Snd(l, Past.Var(l, varname)),
                    (translate_nested_binding (EXPAND(nb, new_varname) :: nbs)))

          | EXPAND_LEFT(Past.BindingUnit(x, t), varname) :: nbs -> 
               Past.Let(l, x, t, Past.Fst(l, Past.Var(l, varname)),
                    translate_nested_binding nbs)
                    
          | EXPAND_RIGHT(Past.BindingUnit(x, t), varname) :: nbs -> 
               Past.Let(l, x, t, Past.Snd(l, Past.Var(l, varname)),
                    translate_nested_binding nbs)

          | [] -> body
     in
     (* Convert the Past.TupleLambda to a series of Past.Let bindings,
      * then call translate_expr to convert the Past.Let bindings to Ast elements
      *)
     (l, "__nb_0", translate_expr (translate_nested_binding [EXPAND(nb, "__nb_0")]))
