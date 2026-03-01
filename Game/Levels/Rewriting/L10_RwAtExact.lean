import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 10
Title "Rewriting in an assumption"

Introduction "
We can rewrite inside an assumption using `rw [h'] at h`, which replaces in assumption `h` according to `h'`.
The `exact` tactic closes the goal when you have an assumption that is exactly the goal.
"

Statement (a b c d : ℝ) (h : c = d * a + b) (h' : b = d) : c = d * a + d := by
  Hint "Rewrite inside `h` using `h'`: `rw [h'] at h`."
  rw [h'] at h
  Hint "Now the assumption `h` is exactly what we need. Use `exact h`."
  exact h

NewTactic exact

Conclusion "
You rewrote in a hypothesis and then used `exact` to finish.
"
