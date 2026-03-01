import Game.Levels.Rewriting.L01_Associativity
import Game.Levels.Rewriting.L02_Expansion
import Game.Levels.Rewriting.L03_RwBasic
import Game.Levels.Rewriting.L04_RwMultiple
import Game.Levels.Rewriting.L05_RwAssumptions
import Game.Levels.Rewriting.L06_ExpAdd
import Game.Levels.Rewriting.L07_ExpSub
import Game.Levels.Rewriting.L08_RwReverse
import Game.Levels.Rewriting.L09_RwReverseEx
import Game.Levels.Rewriting.L10_RwAtExact
import Game.Levels.Rewriting.L11_Calc
import Game.Levels.Rewriting.L12_CalcExp
import Game.Levels.Rewriting.L13_CalcEx

World "Rewriting"
Title "Computing"

Introduction "
# Computing

## The ring tactic

One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
"
