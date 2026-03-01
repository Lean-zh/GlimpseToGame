import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 5
Title "Universal Quantifiers"

Introduction "
# Universal Quantifiers

To prove a goal of the form `∀ x, P x`, you can use `intro x`.
To use an assumption `h : ∀ x, P x`, you can specialize it to a specific value using `specialize h my_value`
or simply apply it to the value: `have hp := h my_value`.
"

Statement (f g : ℝ → ℝ) (h : ∀ x, f x ≤ g x) (h' : g 0 = 0) : f 0 ≤ 0 := by
  Hint "Apply the hypothesis `h` to `0`."
  specialize h 0
  Hint "Now we know `f 0 ≤ g 0`. Use `h'` to finish."
  rw [h'] at h
  exact h

NewTactic specialize

Conclusion "
Universal quantifiers allow us to state properties that hold for all elements of a type.
"
