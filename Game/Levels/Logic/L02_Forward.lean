import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 2
Title "Forward Reasoning"

Introduction "
You can also give a proof with forward reasoning, using the `have` tactic.
In order to announce an intermediate statement we use:

`have my_name : my_statement := by`

and then increase the indentation level.
This triggers the apparition of a new goal: proving the statement.
After the proof is done, the statement becomes available under the name `my_name`.
If the proof is a single `exact` tactic then you can get rid
of `by` and `exact` and directly put the argument of `exact` after the `:=`.
"

Statement (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  Hint "Start by declaring `have h2 : 0 < a^2`."
  have h2 : 0 < a^2 := by
    Hint "Now prove `0 < a^2` using `sq_pos_of_pos` and `ha`."
    apply sq_pos_of_pos
    exact ha
  Hint "Now use `h2` to prove the goal."
  exact sq_pos_of_pos h2

NewTactic «have»
NewTheorem sq_pos_of_pos

Conclusion "
Forward reasoning allows you to build up intermediate facts to reach your goal.
"
