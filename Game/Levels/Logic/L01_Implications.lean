import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 1
Title "Using implications"

Introduction "
# Implications

In Lean, the inhabitants of a proposition are precisely the proofs of that proposition.
Proving an implication `P ⇒ Q` amounts to producing a function that turns proofs of `P`
into proofs of `Q`. Therefore, Lean denotes implication by the symbol `→` instead of `⇒`.

For instance, given a real number `a`, the lemma `sq_pos_of_pos` claims `0 < a → 0 < a^2`
so the proof belows apply the \"function\" `sq_pos_of_pos` to the assumption `ha`.
"

Statement (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  Hint "You can use `exact` to provide the proof term directly."
  exact sq_pos_of_pos ha

NewTheorem sq_pos_of_pos

Conclusion "
The above proof is a direct proof: we already know `0 < a` and we feed this fact into the
implication.
"
