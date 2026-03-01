import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "RewritingAdvanced"
Level 6
Title "calc exercise"

Introduction "
Prove `c = 2*a*d` using `calc` with the given assumptions.
"

Statement (a b c d : ℝ) (h : c = d * a + b) (h' : b = a * d) : c = 2 * a * d := by
  calc
    c = d * a + b   := by rw [h]
    _ = d * a + a * d := by rw [h']
    _ = 2 * a * d   := by ring

Conclusion "
Congratulations! You've learned `ring`, `rw`, `exact`, and `calc`.
"
