import GameServer.Commands
import Game.Library.Basic

World "Logic"
Level 15
Title "Compressed ∀ proof"

Introduction "
We can compress the proof: use `intro hf hg x` and `rw [hf, hg]` in one step.
"

Statement (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x) := by rfl
    _ = f x + g x := by rw [hf, hg]
    _ = (f + g) x := by rfl

Conclusion "
You can often chain rewrites: `rw [hf, hg]` applies both.
"
