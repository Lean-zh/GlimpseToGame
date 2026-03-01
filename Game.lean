import Game.Levels.Rewriting
import Game.Levels.Logic

-- Here's what we'll put on the title screen
Title "Glimpse to Game"
Introduction
"
# Glimpse of Lean

Welcome to this tutorial designed to give you a glimpse of Lean.

This game is split into **Worlds**. Each world focuses on a specific aspect of Lean.

*   **Computing**: Learn how to calculate and rewrite equalities.
*   **Logic**: Learn how to handle logical implications and quantifiers.

Start with the **Computing** world to learn the basics.
"

Info "
Based on the [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) tutorial.
"

Dependency Rewriting → Logic

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
