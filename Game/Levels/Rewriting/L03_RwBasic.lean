import GameServer.Commands
import Game.Library.Basic
import Mathlib.Analysis.Complex.Exponential

World "Rewriting"
Level 3
Title "The rewriting tactic"

Introduction "
Let us now see how to compute using assumptions relating the involved numbers.
This uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the basic Lean tactic for this is `rw`.
Carefully step through the proof below and try to understand what is happening.
"

Statement (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  Hint "Start by rewriting `a` using `{h}`."
  rw [h]
  Hint "Note the goal changed. Now rewrite `b` using `{h'}`."
  rw [h']
  Hint "Now finish with `ring`."
  ring

NewTactic rw

Conclusion "
Note the `rw` tactic changes the current goal. After the first line of the above proof,
the new goal is `b + c + e = d + c`. So you can read this first proof step as saying:
\"I wanted to prove, `a + e = d + c` but, since assumption `h` tells me `a = b + c`,
it suffices to prove `b + c + e = d + c`.\"

The `rw` tactic needs to be told every rewrite step. Later on we will see more powerful tactics
that can automate the tedious steps for you.
"
