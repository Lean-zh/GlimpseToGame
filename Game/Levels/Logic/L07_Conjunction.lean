import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 7
Title "Conjunction"

Introduction "
# Conjunction

To prove `P ∧ Q`, use the `constructor` tactic. This will split the goal into two subgoals: prove `P`, then prove `Q`.
To use an assumption `h : P ∧ Q`, you can decompose it using `rcases h with ⟨hP, hQ⟩` or `have ⟨hP, hQ⟩ := h`.
"

NewTactic rcases

Statement (p q : ℝ → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  rcases h with ⟨x, hx⟩
  use x
  rcases hx with ⟨hp, hq⟩
  constructor
  exact hq
  exact hp

Conclusion "
Conjunction `∧` represents \"and\".
"
