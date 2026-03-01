import GameServer.Commands
import Game.Library.Basic

World "LogicImplications"
Level 3
Title "Proving Implications"

Introduction "
In order to prove an implication, we need to assume the premise and prove the conclusion.
This is done using the `intro` tactic. Secretly the exercise above was proving the
implication `a > 0 → (a^2)^2 > 0` but the premise was already introduced for us.
"

Statement (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  Hint "Use `intro` to bring the assumptions `ha` (for `a > 0`) and `hb` (for `b > 0`) into the context."
  intro ha hb
  Hint "Now use `add_pos` with your new assumptions."
  exact add_pos ha hb

NewTactic intro
NewTheorem add_pos

Conclusion "
Note that, when using `intro`, you need to give a name to the assumption.
Lean will let you use a name that was already used, but the safe
thing to do by default is to use a new name.
"
