import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 27
Title "Using ∃ (rcases)"

Introduction "
For `h : ∃ x, P x`, use `rcases h with ⟨x₀, hx₀⟩` to fix a witness and its proof.
"

Statement (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  rcases h with ⟨k₀, hk₀⟩
  rw [hk₀]
  exact Nat.succ_pos k₀

Conclusion "
`rcases` extracts the witness and proof from an existential.
"
