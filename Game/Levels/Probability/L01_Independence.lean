import GameServer.Commands
import Game.Library.Basic
import Mathlib.Probability.Notation

open MeasureTheory ProbabilityTheory

World "Probability"
Level 1
Title "Independent Sets"

Introduction "
# Independent Sets

Two sets `A` and `B` are independent if `ℙ (A ∩ B) = ℙ A * ℙ B`.
"

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Two sets `A, B` are independent for the ambient probability measure `ℙ` if
`ℙ (A ∩ B) = ℙ A * ℙ B`. -/
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

Statement (A B : Set Ω) : IndepSet A B → IndepSet B A := by
  Hint "Use `IndepSet` definition."
  rw [IndepSet, IndepSet]
  Hint "Commutativity of intersection and multiplication."
  rw [Set.inter_comm, mul_comm]
  intro h
  exact h

NewDefinition IndepSet

Conclusion "
Independence is a symmetric relation.
"
