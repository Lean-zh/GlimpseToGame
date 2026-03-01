import GameServer.Commands
import Game.Library.Basic

World "LogicExists"
Level 1
Title "Conjunction (rcases, constructor)"

Introduction "
For `h : P ∧ Q`, use `rcases h with ⟨hP, hQ⟩` to get `hP : P` and `hQ : Q`.
To prove `P ∧ Q`, use `constructor` to split into two goals.
"

Statement (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

Conclusion "
Conjunction `∧` is \"and\". Use `rcases` to use it, `constructor` to prove it.
"
