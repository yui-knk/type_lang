# Current Status

This language is based on TAPL (Types and Programming Languages) textbook.
Current implementation has almost same features as "fullsimple", which is the theme of chapter 11.

These features are implemented:

- Abs.        "-> x : Bool { x }".
- App.        "(-> x : Bool { x } false)", parens are needed.
- If.         "if true then false else true".
- Let.        "let x = 1 in x".
- As.         "false as Bool".
- Record.     "{10, a=false, true}".
- Projection. "{10, a=false, true}.a".
- Variant.    "case <a=1> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".
- Sequencing. "unit; false".
- Type. Only Bool, Nat, Unit and Arrow (function) types are supported.

These features are not implemented:

- Can not pass a file as input. We should call the excutable with `-e "script"` format.

TODO:

- Record type syntax
- Type alias

# How to implement fix operator

I use big-step structural operational semantics (eval function of Evaluator). I rewrite nodes of AST recursively when evaluate fix operator (eval_fix function calls replace_variable_with_fix_node function). Because if I simply replace `FIX(LAMBDA (x, expr))` to these formats, both of them are recursively evaluated and cause infinite loop:

(1) `LET(x, FIX(LAMBDA (x, expr)), expr)`
(2) `APPLY(LAMBDA(x, expr), FIX(LAMBDA (x, expr)))`

`eval_let` function evaluats bound value first, so `FIX(LAMBDA (x, expr))` is evaluated and generates `LET(x, FIX(LAMBDA (x, expr)), expr)`. This causes infinite loop for (1).
`eval_apply` function evaluats arguments first, so `FIX(LAMBDA (x, expr))` is evaluated and generates `APPLY(LAMBDA(x, expr), FIX(LAMBDA (x, expr)))`. This causes infinite loop for (2).
