import GameServer.Commands
import Game.Library.Basic
import Game.Levels.Analysis.L01_SequenceLimit

World "Analysis"
Level 2
Title "Limit of Sum"

Introduction "
If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`.
You will need to use `rcases` to extract `N` from the limit definitions.
"

Statement (u v : ℕ → ℝ) (l l' : ℝ) (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n hn₁
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n hn₂
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add_le
    _ ≤ ε                                             := by linarith

NewTheorem abs_add_le ge_max_iff
NewTactic rcases

Conclusion "
Great! You proved that the limit of a sum is the sum of the limits.
"
