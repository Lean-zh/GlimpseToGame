import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 25
Title "(p → (q → r)) ↔ p ∧ q → r"

Introduction "
Prove this propositional tautology. You can use `constructor` and `rcases`, or try `tauto`.
"

Statement (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  constructor
  · intro h h'
    rcases h' with ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq

Conclusion "
This equivalence relates curried and uncurried implications.
"
