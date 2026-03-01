import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 26
Title "Existential (use)"

Introduction "
To prove `∃ x, P x`, provide a witness with `use x₀`, then prove `P x₀`.
"

Statement : ∃ n : ℕ, 8 = 2 * n := by
  use 4

Conclusion "
Sometimes the witness is obvious and no further proof is needed.
"
