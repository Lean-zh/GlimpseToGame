import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

open Real

World "Rewriting"
Level 6
Title "Rewriting with a lemma (exp_add)"

Introduction "
We can also use lemmas from the library. For instance `exp_add x y` proves
`exp(x + y) = exp(x) * exp(y)`. We will rewrite twice with this lemma.
"

Statement (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  Hint "First rewrite `exp (a + b + c)` using `exp_add (a + b) c`."
  rw [exp_add (a + b) c]
  Hint "Now rewrite `exp (a + b)` using `exp_add a b`."
  rw [exp_add a b]

NewTheorem Real.exp_add

Conclusion "
You can also write `rw [exp_add, exp_add]` and Lean will rewrite the first matching subexpressions.
"
