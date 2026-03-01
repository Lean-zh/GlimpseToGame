import GameServer.Commands
import Game.Library.Basic

World "SetTheory"
Level 1
Title "Infimum and Supremum"

Introduction "
# Infimum and Supremum

An element `x₀` is an infimum of a set `s` in `X` if every element of `X` is a lower bound of `s` if and only if it is below `x₀`.
"

/-- An element `x₀` is an infimum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it is below `x₀`.  -/
def isInf {X : Type*} [PartialOrder X] (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

Statement {X : Type*} [PartialOrder X] {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by
  Hint "Apply the definition of `isInf` to `x₀`."
  rw [isInf] at h
  rw [h]

NewDefinition isInf lowerBounds

Conclusion "
The infimum is the greatest lower bound.
"
