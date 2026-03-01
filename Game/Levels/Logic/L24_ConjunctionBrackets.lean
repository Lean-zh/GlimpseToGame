import GameServer.Commands
import Game.Library.Basic

World "LogicExists"
Level 2
Title "Conjunction (⟨ , ⟩)"

Introduction "
You can prove `P ∧ Q` using angle brackets: `⟨proof_of_P, proof_of_Q⟩`.
"

Statement (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

Conclusion "
The `⟨a, b⟩` notation constructs a pair (or conjunction).
"
