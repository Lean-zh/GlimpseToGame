import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 17
Title "non_decreasing (forward)"

Introduction "
`non_decreasing f` means `∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂`.
Use forward reasoning: first `have step₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h`, then `exact hg (f x₁) (f x₂) step₁`.
"

Statement (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  have step₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h
  exact hg (f x₁) (f x₂) step₁

NewDefinition non_decreasing

Conclusion "
Composing two non-decreasing functions gives a non-decreasing function.
"
