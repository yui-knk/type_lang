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
- Sequencing. "unit; false".
- Type. Only Bool, Nat, Unit and Arrow (function) types are supported.

These features are not implemented:

- Can not pass a file as input. We should call the excutable with `-e "script"` format.

TODO:

- "{10, a=false, true}.1" access support.
- Should distinguish the type of "{a=false, b=1}" and "{b=1, a=false}" (P.99)
