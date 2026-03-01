import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 12
Title "Proving equivalences (constructor)"

Introduction "
Prove an equivalence using `constructor`, then prove each direction.
Use the focusing dot `·` to separate the two subproofs.
"

Statement (a b : ℝ) : (a - b) * (a + b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b) := by ring
      _ = b^2 + 0 := by rw [h]
      _ = b^2 := by ring
  · intro h
    calc
      (a - b) * (a + b) = a^2 - b^2 := by ring
      _ = b^2 - b^2 := by rw [h]
      _ = 0 := by ring

Conclusion "
The `constructor` tactic splits `P ↔ Q` into two goals: `P → Q` and `Q → P`.
"
