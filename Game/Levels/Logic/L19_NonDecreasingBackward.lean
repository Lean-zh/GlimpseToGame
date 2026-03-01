import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 19
Title "Backward with apply"

Introduction "
You can also use backward reasoning: `apply hg` reduces the goal to `f x₁ ≤ f x₂`,
then `apply hf` reduces it to `x₁ ≤ x₂`, and `exact h` finishes.
"

Statement (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  apply hg
  apply hf
  exact h

NewTactic apply

Conclusion "
`apply` lets Lean infer the arguments via unification.
"
