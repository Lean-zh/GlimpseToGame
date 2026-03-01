import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

open Real

World "Rewriting"
Level 7
Title "exp_sub and exp_zero"

Introduction "
Use `exp_sub x y : exp(x-y) = exp(x) / exp(y)` and `exp_zero : exp 0 = 1`.

Recall that `a + b - c` means `(a + b) - c`.

You can either use `ring` or rewrite with `mul_one x : x * 1 = x` to simplify the denominator on the
right-hand side.
"

Statement (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  Hint "Start by expanding `exp (a + b - c)` using `exp_sub`."
  rw [exp_sub]
  Hint "Now expand `exp (a + b)` using `exp_add`."
  rw [exp_add]
  Hint "Simplify `exp 0` using `exp_zero`."
  rw [exp_zero]
  Hint "Now verify the equality with `ring` or `mul_one`."
  ring

NewTheorem Real.exp_sub Real.exp_zero

Conclusion "
Correct! You used lemmas about `exp` to rewrite the goal.
"
