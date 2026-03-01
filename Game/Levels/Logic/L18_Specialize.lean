import GameServer.Commands
import Game.Library.Basic

World "LogicForall"
Level 5
Title "specialize"

Introduction "
The `specialize` tactic replaces a hypothesis with a specialized instance.
Instead of `have step₁ := hf x₁ x₂ h`, you can write `specialize hf x₁ x₂ h`.
"

Statement (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

Conclusion "
`specialize` is useful when you want to replace an assumption with its instance.
"
