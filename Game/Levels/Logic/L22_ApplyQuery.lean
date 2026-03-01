import GameServer.Commands
import Game.Library.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Support

World "Logic"
Level 22
Title "apply?"

Introduction "
The `apply?` tactic searches the library for lemmas that could solve the goal.
It will suggest tactics — you can click the suggestion to accept it.
"

Statement (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) :
    ∃ x, ∀ y, f x ≤ f y := by
  apply?

Conclusion "
`apply?` is invaluable when you don't remember lemma names.
"
