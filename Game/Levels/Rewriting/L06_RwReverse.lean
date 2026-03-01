import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 6
Title "Rewriting from right to left"

Introduction "
Since equality is a symmetric relation, we can also replace the right-hand side of an
equality by the left-hand side using `←` as in the following example.

Whenever you see in a Lean file a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor above it and learn from a tooltip how to type it.
In the case of ←, you can type it by typing \"\\l \", so backslash-l-space.

Note this rewriting from right to left story is all about sides in the equality you want to
*use*, not about sides in what you want to *prove*. The `rw [← h]` in the previous example
replaced the right-hand side by the left-hand side, so it looked for `b + c` in the current
goal and replaced it with `a`.
"

Statement (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  Hint "Use `{h'}` to replace `c` with `b`."
  rw [←h']
  Hint "Use `{h}` to replace `b + b` with `a`."
  rw [←h]
  Hint "Use `{h''}` to replace `a` with `d`."
  rw [h'']

Conclusion "
Correct! You used reverse rewriting.
"
