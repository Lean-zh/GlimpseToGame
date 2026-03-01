import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "RewritingBasic"
Level 2
Title "Expansion"

Introduction "
It's your turn, replace the word sorry below by a proof. In this case the proof is just `ring`.
After you prove something, you will see a small \"No goals\" message, which is the indication that
your proof is finished.

In the previous example, take a closer look at where Lean displays parentheses.
The `ring` tactic certainly knows about associativity of multiplication, but sometimes
it is useful to understand that binary operation really are binary and an expression like
`a*b*c` is read as `(a*b)*c` by Lean and the fact that this is equal to `a*(b*c)` is a
lemma that is used by the `ring` tactic when needed.
"

Statement (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  Hint "Use `ring` to prove algebraic identities."
  ring

Conclusion "
Correct! `ring` handles expansions too.
"
