import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

open Real

World "Rewriting"
Level 12
Title "calc with exp"

Introduction "
Combine `calc` with `exp_add` to show `exp (2*a) = (exp b)^2 * (exp c)^2` when `a = b + c`.
"

Statement (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by rw [h]
    _ = exp ((b + b) + (c + c))                      := by ring
    _ = exp (b + b) * exp (c + c)                    := by rw [exp_add]
    _ = (exp b * exp b) * (exp c * exp c)            := by rw [exp_add, exp_add]
    _ = (exp b) ^ 2 * (exp c) ^ 2                    := by ring

Conclusion "
You chained equalities using `calc` and `exp_add`.
"
