import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 16
Title "even_fun (g ∘ f)"

Introduction "
Prove that if `f` is even, then `g ∘ f` is even. Note `(g ∘ f)(-x) = g (f (-x))` by definition.
"

Statement (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x)) := by rfl
    _ = g (f x) := by rw [hf]
    _ = (g ∘ f) x := by rfl

Conclusion "
Function composition preserves the even property when the inner function is even.
"
