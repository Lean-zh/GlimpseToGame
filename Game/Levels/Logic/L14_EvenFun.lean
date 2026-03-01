import GameServer.Commands
import Game.Library.Basic

World "LogicForall"
Level 1
Title "even_fun and unfold"

Introduction "
A function `f` is **even** if `∀ x, f (-x) = f x`. We define `even_fun f := ∀ x, f (-x) = f x`.
Use `unfold even_fun` to expand the definition. Use `intro x` to fix an arbitrary `x`.
The first line of the calc uses `rfl` (reflexivity) since `(f + g)(-x)` equals `f (-x) + g (-x)` by definition.
"

Statement (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  unfold even_fun at hf hg
  unfold even_fun
  intro x
  calc
    (f + g) (-x) = f (-x) + g (-x) := by rfl
    _ = f x + g (-x) := by rw [hf x]
    _ = f x + g x := by rw [hg x]
    _ = (f + g) x := by rfl

NewTactic unfold
NewDefinition even_fun

Conclusion "
The `unfold` tactic expands definitions so `rw` can find matching subexpressions.
"
