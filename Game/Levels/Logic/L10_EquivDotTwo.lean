import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 10
Title "Using .2 of equivalence"

Introduction "
For `h : P ↔ Q`, we have `h.1 : P → Q` and `h.2 : Q → P`.
So `(add_le_add_iff_right b).2 ha` proves `0 + b ≤ a + b` from `ha : 0 ≤ a`.
"

Statement {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha

Conclusion "
The `.2` accesses the right-to-left implication of the equivalence.
"
