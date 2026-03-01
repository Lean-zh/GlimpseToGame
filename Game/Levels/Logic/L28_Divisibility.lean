import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 28
Title "Divisibility (a ∣ b)"

Introduction "
`a ∣ b` means `∃ k, b = a * k`. Use `rcases` to extract `k` from `h₁ : a ∣ b`,
then `use k*l` for the goal `a ∣ c` when you have `h₂ : b ∣ c`.
"

Statement (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k * l
  calc
    c = b * l := hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring

Conclusion "
Divisibility is transitive: if `a` divides `b` and `b` divides `c`, then `a` divides `c`.
"
