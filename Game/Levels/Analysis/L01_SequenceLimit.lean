import GameServer.Commands
import Game.Library.Basic

World "Analysis"
Level 1
Title "Sequence Limit Definition"

Introduction "
# Sequence Limits

A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says `u : ℕ → ℝ`.
The definition we'll be using is:

`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of `∀ ε, ε > 0 → _`.
"

/-- Definition of “u tends to l” -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

Statement (u : ℕ → ℝ) (l : ℝ) (h : ∀ n, u n = l) : seq_limit u l := by
  Hint "Start by introducing `ε` and `ε_pos`."
  intro ε ε_pos
  Hint "We need to provide a natural number `N`. Any number will do since the sequence is constant."
  use 0
  Hint "Now introduce `n` and `hn`."
  intro n hn
  Hint "Rewrite `u n` to `l` using `h`."
  rw [h]
  Hint "Simplify `|l - l|`."
  simp
  Hint "Finally, use `linarith` or `exact` to prove `0 ≤ ε`."
  linarith

NewDefinition seq_limit
NewTactic linarith use simp

Conclusion "
If a sequence is constant, it tends to its value.
"
