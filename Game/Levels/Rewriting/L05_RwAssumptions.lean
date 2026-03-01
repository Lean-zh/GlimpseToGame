import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 5
Title "Rewriting with assumptions"

Introduction "
Now try it yourself. Note that `ring` can still do calculations,
but it doesn't use the assumptions `h` and `h'` automatically — you need to rewrite first.
"

Statement (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  Hint "Rewrite using `h'` and `h` to simplify the goal (e.g. `rw [h', h]`)."
  rw [h', h]
  Hint "Now verify the equality with `ring`."
  ring

Conclusion "
Correct! You used local assumptions with `rw` then `ring`.
"
