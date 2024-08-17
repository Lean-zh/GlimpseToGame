import GameServer.Commands

-- import all worlds
import Game.Levels.Introduction
import Game.Levels.Basics
import Game.Levels.Topics

Title "GlimpseOfLean Game"

Introduction "
Welcome to the GlimpseOfLean game! This game is designed to introduce you to theorem proving in Lean.
Click on a world to start.
"

Info "
This game has been developed to give you a glimpse of Lean in a couple of hours.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
