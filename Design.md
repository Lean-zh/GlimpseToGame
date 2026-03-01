# Glimpse to Game Design Document

## 1. Game Overview
**Title**: Glimpse to Game  
**Goal**: Convert the *Glimpse of Lean* tutorial into an interactive game format using the `lean4game` engine.  
**Target Audience**: Mathematicians and students interested in Lean 4 who prefer a gamified, step-by-step learning experience.

## 2. World Structure

The game is organized into "Worlds", each focusing on specific tactics and logical concepts.

### World 1: Computing (Rewriting)
*   **Source**: `GlimpseOfLean/Exercises/01Rewriting.lean`
*   **Focus**: Basic equality and calculation.
*   **Key Tactics**: `ring`, `rw`, `calc`.
*   **Levels**:
    1.  Associativity (`ring`)
    2.  Expansion (`ring`)
    3.  Basic Rewriting (`rw`)
    4.  Multiple Rewrites (`rw`)
    5.  Rewriting with Lemmas (`rw` with args)
    6.  Reverse Rewriting (`rw [← h]`)
    7.  Calculation Layout (`calc`)

### World 2: Logic (Basics)
*   **Source**: `GlimpseOfLean/Exercises/02Iff.lean`, `03Forall.lean`, `04Exists.lean`
*   **Focus**: Propositional logic and quantifiers.
*   **Key Tactics**: `exact`, `apply`, `intro`, `have`, `constructor`, `rcases`, `use`.
*   **Levels**:
    1.  Implications (Using `→`)
    2.  Forward Reasoning (`have`)
    3.  Proving Implications (`intro`)
    4.  Equivalences (`↔`, `rw` with iff)
    5.  Universal Quantifiers (`∀`)
    6.  Existential Quantifiers (`∃`, `use`)
    7.  Conjunctions (`∧`, `constructor`)

### World 3+: Advanced Topics (Planned)
*   **Classical Logic**: `Topics/ClassicalPropositionalLogic.lean`
*   **Set Theory**: `Topics/GaloisAdjunctions.lean`
*   **Analysis**: `Topics/SequenceLimits.lean`
*   **Algebra**: `Topics/RingTheory.lean`

## 3. Navigation & Dependency
*   **Start**: Computing World
*   **Unlock**: Logic World (after Computing)
*   **Unlock**: Topic Worlds (after Logic)

## 4. UI/UX Improvements
*   **Title Screen**: Clear introduction to Lean.
*   **Side Panel**: Helpful hints in every level.
*   **Inventory**: Tactic documentation should be gradually revealed.

## 5. Development Guidelines
*   **Porting**: Copy content from `GlimpseOfLean`, converting `example` to `Statement`.
*   **Hints**: Convert comments into interactive `Hint` blocks.
*   **Verification**: Ensure all levels are solvable and build successfully.
