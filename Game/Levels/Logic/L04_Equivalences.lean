import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 4
Title "Equivalences"

Introduction "
# Equivalences

The equivalence `A ↔ B` is just the conjunction of `A → B` and `B → A`.
You can prove it using `constructor` if the goal is `A ↔ B`.
If you have an assumption `h : A ↔ B`, you can use `rw [h]` to replace `A` with `B`.
"

Statement (a b c : ℝ) : a + b = c ↔ a = c - b := by
  Hint "We can prove this equivalence by proving both directions."
  constructor
  Hint "First direction: assume `a + b = c`, prove `a = c - b`."
  intro h
  rw [← h]
  ring
  Hint "Second direction: assume `a = c - b`, prove `a + b = c`."
  intro h
  rw [h]
  ring

NewTactic constructor

Conclusion "
Equivalences are powerful because they allow you to rewrite propositions.
"
