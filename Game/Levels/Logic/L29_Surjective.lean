import GameServer.Commands
import Game.Library.Basic
open Function

World "LogicExists"
Level 7
Title "Surjective"

Introduction "
`Surjective f` means `∀ y, ∃ x, f x = y`. Use `intro y` and `rcases h y with ⟨w, hw⟩`,
then `use f w` (or another suitable witness).
"

Statement (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  intro y
  rcases h y with ⟨w, hw⟩
  use f w
  exact hw

Conclusion "
If `g ∘ f` is surjective, then `g` is surjective.
"
