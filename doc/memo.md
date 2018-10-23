# Current Status

This language is based on TAPL (Types and Programming Languages) textbook.
Current implementation has almost same features as "fullpoly", which is the theme of chapter 23.

These features are implemented:

- Abs.        "-> x : Bool { x }".
- App.        "-> x : Bool { x }.(false)".
- If.         "if true then false else true".
- Let.        "let x = 1 in x".
- As.         "false as Bool".
- Record.     "{10, a=false, true}".
- Projection. "{10, a=false, true}.a".
- Variant.    "case <a=1> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".
- Sequencing. "unit; false".
- Ref.        "ref true".
- Deref.      "! ref true".
- Assign.     "let x = ref false in x := true".
- TyAbs.      "-> X { false }".
- TyApply.    "-> X { false } [Nat]".
- Pack.       "{*Nat, { a=0, f=-> x:Nat { succ(x) }}} as { Some X, { a:X, f:X -> Nat }}".
- Unpack.     "let {X, x} = packed in x.f.(x.a)".

These types are implemented:

- Arrow (function)
- Bool
- Nat
- Record
- Variant
- Unit
- Ref
- Top
- All (Universal type)
- Some (Existential type)

These features are not implemented:

- Can not pass a file as input. We should call the excutable with `-e "script"` format.

TODO:

- Ref type syntax
- Type alias
- Type variable dereference in type_ckeck (type_of function) ?

# How to implement fix operator

I use big-step structural operational semantics (eval function of Evaluator). I rewrite nodes of AST recursively when evaluate fix operator (eval_fix function calls replace_variable_with_fix_node function). Because if I simply replace `FIX(LAMBDA (x, expr))` to these formats, both of them are recursively evaluated and cause infinite loop:

(1) `LET(x, FIX(LAMBDA (x, expr)), expr)`
(2) `APPLY(LAMBDA(x, expr), FIX(LAMBDA (x, expr)))`

`eval_let` function evaluats bound value first, so `FIX(LAMBDA (x, expr))` is evaluated and generates `LET(x, FIX(LAMBDA (x, expr)), expr)`. This causes infinite loop for (1).
`eval_apply` function evaluats arguments first, so `FIX(LAMBDA (x, expr))` is evaluated and generates `APPLY(LAMBDA(x, expr), FIX(LAMBDA (x, expr)))`. This causes infinite loop for (2).

# Why direct evaluating does not work well

Evaluating Node to Value by `eval` function is very straightforward way. But this approach does not work well when implementing reference with store because we can make reference for lambda value. When we deref location and get lambda value in the context of "apply", we should apply the argument to the lambda. If we store the lambda value as `Value`, we should de-construct the lambda value in `eval` function. Introduce "value node" concept to make it easy to handle these situation.

Ref: 5542d5c00e30aafed15ceb1915d394befafe6750

# How to implement Ref, Deref and Assign

## Type check

Store is not needed on type check phase because Ref term itself has ref type (e.g. ref bool).

## Evaluation

Store is needed on evaluation phase. Loc node is introduced to represent the location on store. Ref node is evaluated to the location. Store can be accessed by the location.

# Links

- https://www.cis.upenn.edu/~bcpierce/tapl/
