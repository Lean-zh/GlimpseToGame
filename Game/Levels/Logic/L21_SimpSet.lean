import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 21
Title "simp (Set)"

Introduction "
The `simp` tactic simplifies goals using a set of lemmas. For sets, it knows
that `x ∈ (X ∩ Y) ∪ (X \\ Y)` when `x ∈ X`.
"

Statement (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  simp
  exact hx

NewTactic simp

Conclusion "
`simp` automates many routine simplifications.
"
