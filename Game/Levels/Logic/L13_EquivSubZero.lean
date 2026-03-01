import GameServer.Commands
import Game.Library.Basic

World "LogicImplications"
Level 13
Title "a = b ↔ b - a = 0"

Introduction "
Prove this equivalence using `constructor` and then each direction.
"

Statement (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    calc
      a = b - (b - a) := by ring
      _ = b - 0 := by rw [h]
      _ = b := by ring

Conclusion "
You've mastered proving equivalences with `constructor`.
"
