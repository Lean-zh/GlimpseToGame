import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 8
Title "Rewriting from right to left"

Introduction "
Since equality is symmetric, we can replace the *right*-hand side of an equality
by the *left*-hand side using `←` (type with \\l ). So `rw [← h]` looks for the
right-hand side of `h` in the goal and replaces it with the left-hand side.
"

Statement (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  Hint "Use `rw [← h]` to replace `b + c` in the goal with `a`."
  rw [← h]
  Hint "Now use `h'` to finish."
  rw [h']

Conclusion "
The `←` means we use the equality from right to left.
"
