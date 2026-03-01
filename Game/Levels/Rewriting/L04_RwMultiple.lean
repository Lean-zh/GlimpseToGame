import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 4
Title "Multiple rewrites"

Introduction "
One can actually do several rewritings in one command.
`rw [h, h']` rewrites using `h` then `h'` in a single step.
"

Statement (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  Hint "Rewrite both assumptions in one command: `rw [h, h']`."
  rw [h, h']
  ring

Conclusion "
Good job! You can combine rewrites in one command.
"
