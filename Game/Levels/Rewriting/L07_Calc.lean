import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 7
Title "Calculation layout using calc"

Introduction "
What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout (and also return to using `ring`
instead of explicit lemma invocations).
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand on the first line).
Carefully check you understand this by putting your cursor after each `by` and looking
at the tactic state.
"

Statement (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring

Conclusion "
Congratulations, this is the end of your first exercise file! You've seen what typing
a Lean proof looks like and have learned about the following tactics:
* `ring`
* `rw`
* `exact`
* `calc`
"
