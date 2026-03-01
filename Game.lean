import Game.Levels.Rewriting
import Game.Levels.Logic
import Game.Levels.Analysis

-- Here's what we'll put on the title screen
Title "Glimpse to Game"
Introduction
"
# Glimpse of Lean

Welcome to this tutorial designed to give you a glimpse of Lean.

This game is split into **Worlds**. Each world focuses on a specific aspect of Lean.

*   **Computing**: Learn how to calculate and rewrite equalities.
*   **Logic**: Learn how to handle logical implications and quantifiers.
*   **Analysis**: Learn how to handle limits of sequences.

Start with the **Computing** world to learn the basics.
"

Info "
Based on the [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) tutorial.
"

Dependency Rewriting → Logic
Dependency Logic → Analysis

/-! Information to be displayed on the servers landing page. -/
Languages "en" "zh"
CaptionShort "Glimpse of Lean tutorial gamified"
CaptionLong "Interactive version of the Glimpse of Lean tutorial. Learn the basics of Lean 4 including rewriting, logic, and analysis through a series of puzzles."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
