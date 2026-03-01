import GameServer.Commands
import Game.Library.Basic

World "LogicForall"
Level 7
Title "non_increasing (g ∘ f)"

Introduction "
`non_increasing f` means `∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂`.
When `f` is non-decreasing and `g` is non-increasing, `g ∘ f` is non-increasing.
"

Statement (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  intro x₁ x₂ h
  have step₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h
  exact hg (f x₁) (f x₂) step₁

NewDefinition non_increasing

Conclusion "
Composing increasing with decreasing gives decreasing.
"
