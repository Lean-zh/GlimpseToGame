import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "RewritingBasic"
Level 1
Title "The ring tactic"

Introduction "
One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
"

Statement (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

NewTactic ring

Conclusion "
Great! The `ring` tactic handles basic algebraic identities.
"
