import GameServer.Commands
import Game.Library.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real

World "LogicForall"
Level 9
Title "apply?"

Introduction "
The `apply?` tactic searches the library for lemmas that could solve the goal.
It will suggest tactics — you can click the suggestion to accept it.
Use `Continuous.exists_forall_le_of_hasCompactSupport` (the additive version of the theorem).
"

Statement (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) :
    ∃ x, ∀ y, f x ≤ f y := by
  exact hf.exists_forall_le_of_hasCompactSupport h2f

Conclusion "
`apply?` is invaluable when you don't remember lemma names.
"
