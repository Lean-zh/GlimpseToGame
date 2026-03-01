import GameServer.Commands
import Game.Library.Basic

World "LogicImplications"
Level 9
Title "add_le_add_iff_right"

Introduction "
`add_le_add_iff_right c` states `a + c ≤ b + c ↔ a ≤ b`.
Prove the variation using `sub_nonneg` and `ring`.
"

Statement {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  rw [← sub_nonneg]
  ring
  rw [sub_nonneg]

Conclusion "
This lemma is in mathlib as `add_le_add_iff_right`.
"
