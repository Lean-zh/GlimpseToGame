import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "RewritingAdvanced"
Level 4
Title "Calculation layout (calc)"

Introduction "
The `calc` tactic gives a natural layout for chain of equalities.
After each `:=`, the goal is to prove that line equals the previous right-hand side (or the first left-hand side).
Use `_` for the right-hand side of the previous line.
"

Statement (a b c d : ℝ) (h : c = b * a - d) (h' : d = a * b) : c = 0 := by
  rw [h]
  rw [h']
  ring

NewTactic «calc»

Conclusion "
The `calc` block makes proof steps readable like on paper.
"
