# Current Status

This language is based on TAPL (Types and Programming Languages) textbook.
Current implementation has almost same features as "simplebool", which is the theme of chapter 10.

These features are implemented:

- Abs. "-> x : Bool { x }".
- App. "(-> x : Bool { x } false)", parens are needed.
- If. "if true then false else true".
- Type. Only Bool and Arrow (function) types are supported.

These features are not implemented:

- Can not pass a file as input. We should call the excutable with `-e "script"` format.
- Does not support newline ('\n').
