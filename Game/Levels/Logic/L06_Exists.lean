import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 6
Title "Existential Quantifiers"

Introduction "
# Existential Quantifiers

To prove a goal of the form `∃ x, P x`, you need to provide a witness `w` such that `P w` holds.
This is done using the `use` tactic.
To use an assumption `h : ∃ x, P x`, you can decompose it using `rcases h with ⟨x, hx⟩`.
"

Statement : ∃ x : ℝ, x + 1 = 2 := by
  Hint "Provide a real number `x` such that `x + 1 = 2`."
  use 1
  Hint "Now prove `1 + 1 = 2`."
  norm_num

NewTactic use

Conclusion "
Existential quantifiers assert the existence of an element satisfying a property.
"
