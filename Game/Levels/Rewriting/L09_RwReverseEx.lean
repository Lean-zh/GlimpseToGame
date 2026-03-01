import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 9
Title "Reverse rewriting exercise"

Introduction "
Practice reverse rewriting. Use `rw [← h]` to replace the right-hand side of `h` with its left-hand side in the goal.
"

Statement (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  Hint "Use `{h'}` to replace `c` with `b`: `rw [← h']`."
  rw [← h']
  Hint "Use `{h}` to replace `b + b` with `a`: `rw [← h]`."
  rw [← h]
  Hint "Use `{h''}` to replace `a` with `d`: `rw [h'']`."
  rw [h'']

Conclusion "
Correct! You used reverse rewriting.
"
