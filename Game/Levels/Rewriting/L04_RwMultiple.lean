import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 4
Title "Multiple rewrites"

Introduction "
One can actually do several rewritings in one command.
`rw [h, h']` rewrites `h` then `h'`.

Now try it yourself. Note that `ring` can still do calculations,
but it doesn't use the assumptions `h` and `h'`.
"

Statement (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  Hint "Try rewriting both `{h}` and `{h'}`. You can do it in one command `rw [{h}, {h'}]` or two."
  rw [h', h]
  Hint "Now verify the equality with `ring`."
  ring

Conclusion "
Good job! You can combine rewrites.
"
