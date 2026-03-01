import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 11
Title "add_le_add_iff_left"

Introduction "
Use `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` to prove `a ≤ a + b` when `0 ≤ b`.
"

Statement (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  calc
    a = a + 0 := by ring
    _ ≤ a + b := by exact (add_le_add_iff_left a).2 hb

Conclusion "
You used the left variant of the addition-order equivalence.
"
