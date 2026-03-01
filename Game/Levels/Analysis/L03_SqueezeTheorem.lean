import GameServer.Commands
import Game.Library.Basic
import Game.Levels.Analysis.L01_SequenceLimit

World "Analysis"
Level 3
Title "Squeeze Theorem"

Introduction "
# Squeeze Theorem

If `u n ≤ v n ≤ w n` and `u` and `w` both tend to `l`, then `v` also tends to `l`.
"

Statement (u v w : ℕ → ℝ) (l : ℝ) (hu : seq_limit u l) (hw : seq_limit w l)
    (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  intro ε ε_pos
  specialize hu ε ε_pos
  rcases hu with ⟨N, hN⟩
  specialize hw ε ε_pos
  rcases hw with ⟨M, hM⟩
  use max N M
  intro n hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hnN, hnM⟩
  specialize hN n hnN
  specialize hM n hnM
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  · linarith
  · linarith

Conclusion "
The Squeeze Theorem is a fundamental tool for proving limits.
"
