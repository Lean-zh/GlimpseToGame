import GameServer.Commands
import Game.Library.Basic

World "Algebra"
Level 1
Title "Ring Homomorphisms"

Introduction "
# Ring Homomorphisms

Given a ring `R` and a ring `S`, a ring homomorphism from `R` to `S` is written `f : R →+* S`.
It preserves addition, multiplication, zero, and one.
"

Statement {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : R) :
    f (1 + x * y) + f 0 = 1 + f x * f y := by
  Hint "Use `simp` to simplify ring homomorphisms."
  simp

Conclusion "
`simp` is very effective at simplifying expressions involving ring homomorphisms.
"
