import GameServer.Commands
import Game.Library.Basic
import Game.Levels.Analysis.L01_SequenceLimit

World "Analysis"
Level 4
Title "Uniqueness of Limits"

Introduction "
# Uniqueness of Limits

A sequence cannot converge to two different limits.
"

Statement (u : ℕ → ℝ) (l l' : ℝ) (hl : seq_limit u l) (hl' : seq_limit u l') : l = l' := by
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  specialize hN (max N N') (le_max_left N N')
  specialize hN' (max N N') (le_max_right N N')
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_sub_le
    _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
    _ ≤ ε := by linarith

NewTheorem eq_of_abs_sub_le_all abs_sub_le abs_sub_comm

Conclusion "
Limits are unique in Hausdorff spaces (like ℝ).
"
