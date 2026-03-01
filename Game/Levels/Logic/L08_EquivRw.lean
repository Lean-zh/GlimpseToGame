import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 8
Title "Equivalences (rw with ↔)"

Introduction "
We can rewrite using equivalences with the `rw` tactic. The lemma
`sub_nonneg : 0 ≤ y - x ↔ x ≤ y` relates subtraction to ordering.
Use `rw [← sub_nonneg]` to replace `0 ≤ ...` by `... ≤ ...`.
"

Statement {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  Hint "Start with `rw [← sub_nonneg]` to transform the left side."
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a := by ring
  rw [key]
  rw [sub_nonneg]

Conclusion "
Equivalences allow rewriting in both directions.
"
